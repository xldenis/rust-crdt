use serde::Serialize;
use serde::de::DeserializeOwned;

use error::Result;
use traits::ComposableCrdt;
use vclock::VClock;
use std::collections::{BTreeMap, BTreeSet};

/// The Map CRDT allows for composition of CRDT's
#[derive(Debug, Clone, PartialEq)]
pub struct Map<K, V, A> where
    K: Ord + Clone + Serialize + DeserializeOwned,
    V: Clone + Serialize + DeserializeOwned + ComposableCrdt<A>,
    A: Ord + Clone + Serialize + DeserializeOwned
{
    clock: VClock<A>,
    entries: BTreeMap<K, MapEntry<V, A>>,
    deferred: BTreeMap<VClock<A>, BTreeSet<K>>
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct MapEntry<V, A> where
    V: Clone + Serialize + DeserializeOwned + ComposableCrdt<A>,
    A: Ord + Clone + Serialize + DeserializeOwned
{
    // Clock stores the actors and actors versions at the time of last change.
    // This clock is here only to decide if an entry is removed or not on conflicts.
    //
    // We compare this entry clock to the Map.clock to decide add/remove conflicts
    // e.g. say replica A has key `"user_32"` but replica B does not. We need to decide
    // whether replica B has processed a `remove("user_32")` operation and replica A has
    // not or replica A has processed an insert(("key", Orswot)) operation which has not
    // been seen by replica B yet.
    //
    // This conflict can be resolved by comparing replica B's Map.clock to the "user_32"
    // entries clock in replica A.
    // If B's clock is a descendent of this "user_32"'s clock, then we know that B has
    // seen this entry and removed it, otherwise we assume B has not received the insert
    // operation and we will keep the key.
    clock: VClock<A>,

    // The nested CRDT
    val: V,
    
    // Tombstone is an empty V with clock set to the (vclock) time of the latest remove
    // operation. This tombstone is always merged into values to give us the Reset-Remove semantics.
    // It says: any operations happening before this tombstones clock are discarded.
    tombstone: V
}

impl<K, V, A> ComposableCrdt<A> for Map<K, V, A> where
    K: Ord + Clone + Serialize + DeserializeOwned,
    V: Clone + Serialize + DeserializeOwned + ComposableCrdt<A>,
    A: Ord + Clone + Serialize + DeserializeOwned
{
    // set's the clock of the map.
    // Used by a containing map to track causality when updating sub-crdt's
    fn set_clock(&mut self, clock: VClock<A>) {
        self.clock = clock;
    }

    fn merge(&mut self, other: &Self) -> Result<()> {
        self.clock.merge(&other.clock);
        for (key, entry) in other.entries.iter() {
            let existing_entry = self.entries.entry(key.clone())
                .or_insert_with(|| entry.clone());

            existing_entry.clock.merge(&entry.clock);
            existing_entry.val.merge(&entry.val)?;
            existing_entry.tombstone.merge(&entry.tombstone)?;
            existing_entry.val.merge(&existing_entry.tombstone)?;
        }

        for (ctx, keys) in other.deferred.iter() {
            if !(&self.clock >= ctx) {
                let mut existing_keys = self.deferred.entry(ctx.clone())
                    .or_insert_with(|| BTreeSet::default());
                existing_keys.extend(keys.iter().cloned());
            }
        }

        let new_deferred: BTreeMap<VClock<A>, BTreeSet<K>> = self.deferred.iter()
            .filter(|(ctx, _)| !(&self.clock > ctx))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();

        // now apply the deferred removes
        for (ctx, key_set) in new_deferred.iter() {
            for key in key_set.iter().cloned() {
                self.remove_with_ctx(key, ctx.clone());
            }
        }

        let mut to_remove = Vec::new();
        for (key, entry) in self.entries.iter() {
            if other.entries.get(&key).is_none() && other.clock >= entry.clock{
                to_remove.push(key.clone());
            }
        }

        for key in to_remove.into_iter() {
            self.remove_with_ctx(key, other.clock.clone());
        }
        Ok(())
    }
}

impl<K, V, A> Default for Map<K, V, A> where
    K: Ord + Clone + Serialize + DeserializeOwned,
    V: Clone + Serialize + DeserializeOwned + ComposableCrdt<A>,
    A: Ord + Clone + Serialize + DeserializeOwned
{
    fn default() -> Self {
        Map::new()
    }
}

impl<K, V, A> Map<K, V, A> where
    K: Ord + Clone + Serialize + DeserializeOwned,
    V: Clone + Serialize + DeserializeOwned + ComposableCrdt<A>,
    A: Ord + Clone + Serialize + DeserializeOwned
{
    /// Constructs an empty Map
    pub fn new() -> Map<K, V, A> {
        Map {
            clock: VClock::new(),
            entries: BTreeMap::new(),
            deferred: BTreeMap::new()
        }
    }

    /// Returns the number of entries in the Map
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Get a reference to a value under some key
    pub fn get(&self, key: &K) -> Option<&V> {
        self.entries.get(&key)
            .map(|map_entry| &map_entry.val)
    }

    /// inserts adds `(key, val.kind()) -> val` mapping to the Map.
    ///
    /// !! NOTE:  potentially unexpected behaviour
    /// !! 1. this map stores multiple entries under the same `key` if they are of different kind().
    /// e.g.
    /// ``` rust
    /// use crdts::{Map, LWWReg};
    /// let mut ages: Map<String, LWWReg<u16, u16>, String> = Map::new();
    /// assert_eq!(ages.insert("bob".into(), LWWReg { val: 48, dot: 0 }, "A".into()), None);
    /// assert_eq!(ages.get(&"bob".into()), Some(&LWWReg { val: 48, dot: 0 }));
    /// ```
    ///
    /// !! 2. `insert()` destroy causality! think of it as the equivalent of removing and adding a new element.
    ///       if you want to update a crdt while preserving causal history, consider using `update()`.
    pub fn insert(&mut self, key: K, val: V, actor: A) {
        let mut clock = VClock::new();
        // this witness() should never fail since this clock is brand new
        let actor_version = self.clock.get(&actor).unwrap_or(0);
        clock.witness(actor,  actor_version + 1).unwrap();
        self.insert_with_ctx(key, val, clock);
    }

    /// Same as insert but instead of using a bumped map clock, you provide your own
    pub fn insert_with_ctx(&mut self, key: K, val: V, ctx: VClock<A>) {
        if !(self.clock >= ctx) {
            self.clock.merge(&ctx);
            let mut tombstone = V::default();
            tombstone.set_clock(ctx.clone());
            self.entries.insert(key, MapEntry { clock: ctx, val, tombstone });
        }
    }

    /// Update a nested CRDT preserving causality
    ///
    /// If an entry doesn't exist, the `default` function will be used to
    /// create an entry prior to updater being called.
    /// ``` rust
    /// use crdts::{Map, LWWReg};
    ///
    /// let mut meredith: Map<String, LWWReg<u64, (u64, String)>, String> = Map::new();
    /// let actor = "actor_1".to_string();
    ///
    /// assert_eq!(meredith.len(), 0);
    ///
    /// meredith.update(
    ///   "age".into(),
    ///   |mut reg: LWWReg<u64, (u64, String)>| {
    ///       reg.update(48, (73, actor.clone()));
    ///       Some(reg)
    ///   },
    ///   actor.clone()
    /// );
    /// 
    /// assert_eq!(
    ///     meredith.get(&"age".into()),
    ///     Some(&LWWReg { val: 48, dot: (73, "actor_1".into()) })
    /// );
    ///
    /// assert_eq!(meredith.len(), 1);
    ///
    /// meredith.update(
    ///   "age".into(),
    ///   |mut reg: LWWReg<u64, (u64, String)>| {
    ///       if reg.val > 21 {
    ///           None
    ///       } else {
    ///           Some(reg)
    ///       }
    ///   },
    ///   actor.clone()
    /// );
    ///
    /// assert_eq!(meredith.get(&"age".into()), None);
    /// assert_eq!(meredith.len(), 0);
    /// ```
    pub fn update(
        &mut self,
        key: K,
        mut updater: impl FnMut(V) -> Option<V>,
        actor: A
    ) {
        let update_res = match self.entries.remove(&key) {
            Some(MapEntry {val, ..}) =>  {
                updater(val)
            },
            None => {
                updater(V::default())
            }
        };

        if let Some(val) = update_res {
            self.insert(key, val, actor);
        } else {
            self.remove(key, actor);
        }
    }

    /// Same as update() but instead of bumping the map's clock, you provide your own context
    pub fn update_with_ctx(
        &mut self,
        key: K,
        mut updater: impl FnMut(V) -> Option<V>,
        ctx: VClock<A>
    ) {
        if !(self.clock >= ctx) {
            let update_res = match self.entries.remove(&key) {
                Some(MapEntry {val, ..}) =>  {
                    updater(val)
                },
                None => {
                    updater(V::default())
                }
            };

            if let Some(val) = update_res {
                self.insert_with_ctx(key, val, ctx);
            } else {
                self.remove_with_ctx(key, ctx);
            }
        }
    }

    /// Remove a key from the Map
    pub fn remove(&mut self, key: K, actor: A) {
        let mut ctx = self.clock.clone();
        ctx.increment(actor);
        self.remove_with_ctx(key, ctx);
    }

    /// Removes an entry from the map under a given context.
    /// If the given context is a descended of the map's clock,
    /// we store a deferred remove action.
    pub fn remove_with_ctx(&mut self, key: K, ctx: VClock<A>) {
        if !(self.clock >= ctx) {
            // We need to defer this remove because our clock does not
            // descend from the context clock.
            // There could be more operations between the map clock and the
            // ctx clock which could invalidate this remove if we don't
            // store the remove as deferred
            {
                let deferred_set = self.deferred.entry(ctx.clone())
                    .or_insert_with(|| BTreeSet::new());
                deferred_set.insert(key.clone());
                println!("inserted deferred");
            }
            // Check the older contexts for removes of the same key.
            // This remove obsoletes any previous remove so we cleanup a bit
            let mut obsolete_ctxs = Vec::new();
            for (o_ctx, mut o_set) in self.deferred.iter_mut().filter(|(pre_ctx, _)| pre_ctx < &&ctx) {
                o_set.remove(&key);
                if o_set.is_empty() {
                    obsolete_ctxs.push(o_ctx.clone());
                }
            }
            for obsolete_ctx in obsolete_ctxs.into_iter() {
                self.deferred.remove(&obsolete_ctx);
            }
        }

        let should_rm = if let Some(mut map_entry) = self.entries.get_mut(&key) {
            if ctx >= map_entry.clock {
                // ctx has seen this entry so we can remove it
                true
            } else {
                // otherwise update the tombstone to have no data as of the
                // greatest-lower-bound of the context and map clock.
                //
                // This says that at this lower clock bound, entry was the
                // `default` value of the crdt (empty set / empty map / etc.)
                //
                // This is used to provide the reset-remove semantics
                // ie. if one replica removes a key while another updates
                //     the a key, on merge, only the updated datat will
                //     survive, all else is removed.
                map_entry.tombstone.set_clock(VClock::glb(&ctx, &self.clock));
                false
            }
        } else {
            false
        };

        if should_rm {
            self.entries.remove(&key);
        }

        // finally update the map clock
        self.clock.merge(&ctx);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    use lwwreg::LWWReg;
    use orswot::Orswot;

    use quickcheck::{Arbitrary, Gen, TestResult};


    #[derive(Debug, Clone, PartialEq)]
    enum Op {
        Remove(u8, VClock<u16>),
        Insert(u8, (u8, u64, u16), VClock<u16>),
        Update(u8, Option<(u8, u64, u16)>, VClock<u16>),
    }

    impl Op {
        fn apply(&self, map: &mut Map<u8, LWWReg<u8, (u64, u16)>, u16>) {
            match self.clone() {
                Op::Remove(key, ctx) => {
                    map.remove_with_ctx(key, ctx);
                },
                Op::Insert(key, (val, time, actor), ctx) => {
                    map.insert_with_ctx(key, LWWReg { val: val, dot: (time, actor) }, ctx);
                },
                Op::Update(key, None, ctx) => {
                    map.update_with_ctx(key, |_| None, ctx);
                }
                Op::Update(key, Some((val, dot, actor)), ctx) => {
                    map.update_with_ctx(key, |mut reg| {
                        reg.update(val, (dot, actor)).unwrap();
                        Some(reg)
                    }, ctx);
                }
                            
            };
        }
    }

    impl Arbitrary for Op {
        fn arbitrary<G: Gen>(g: &mut G) -> Op {
            let val: u8 = g.gen();
            let time: u64 = g.gen();
            let actor: u16 = g.gen();
            let key: u8 = g.gen();
            let ctx: VClock<u16> = VClock::arbitrary(g);
            let choices = [
                Op::Remove(key, ctx.clone()),
                Op::Insert(key, (val, time, actor), ctx.clone()),
                Op::Update(key, *(g.choose(&[None, Some((val, time, actor))]).unwrap()), ctx)
            ];
            let op = g.choose(&choices).unwrap();
            op.clone()
        }

        fn shrink(&self) -> Box<Iterator<Item = Op>> {
            let vec: Vec<Op> = match self.clone() {
                Op::Remove(key, ctx) => 
                    vec![Op::Remove(key/2, ctx.clone())]
                    .into_iter()
                    .filter(|op| op != self)
                    .chain(
                        ctx.shrink().map(|c| Op::Remove(key, c))
                    )
                    .collect(),
                Op::Insert(key, (val, time, actor), ctx) =>
                    vec![Op::Insert(key/2, (val, time, actor),   ctx.clone()),
                         Op::Insert(key,   (val/2, time, actor), ctx.clone()),
                         Op::Insert(key,   (val, time/2, actor), ctx.clone()),
                         Op::Insert(key,   (val, time, actor/2), ctx.clone())]
                    .into_iter()
                    .filter(|op| op != self)
                    .chain(ctx.shrink().map(|c| {
                        Op::Insert(key, (val, time, actor), c)
                    }))
                    .collect(),
                Op::Update(key, None, ctx) =>
                    vec![Op::Update(key/2, None, ctx.clone()),
                         Op::Remove(key, ctx.clone())
                    ]
                    .into_iter()
                    .filter(|op| op != self)
                    .chain(
                        ctx.shrink().map(|c| Op::Update(key, None, c))
                    )
                    .collect(),
                Op::Update(key, Some((val, time, actor)), ctx) =>
                    vec![Op::Update(key/2, Some((val, time, actor)), ctx.clone()),
                         Op::Update(key,   Some((val/2, time, actor)), ctx.clone()),
                         Op::Update(key,   Some((val, time/2, actor)), ctx.clone()),
                         Op::Update(key,   Some((val, time, actor/2)), ctx.clone()),
                         Op::Update(key,   None, ctx.clone())]
                    .into_iter()
                    .filter(|op| op != self)
                    .chain(
                        ctx.shrink().map(|c| Op::Update(key, Some((val, time, actor)), c))
                    )
                    .collect(),
            };
            Box::new(vec.into_iter())
        }
    }

    #[test]
    fn test_new() {
        let m: Map<u16, LWWReg<u16, u16>, String> = Map::new();
        assert_eq!(m.len(), 0);
    }

    #[test]
    fn test_default() {
        let m: Map<u16, LWWReg<u16, u16>, String> = Map::default();
        assert_eq!(m, Map::new());
        assert_eq!(m.len(), 0);
    }

    #[test]
    fn test_get() {
        let mut m: Map<u16, LWWReg<u16, u16>, String> = Map::new();
        
        assert_eq!(m.get(&0), None);

        m.clock.increment("actor 1".into());
        m.entries.insert(0, MapEntry {
            clock: m.clock.clone(),
            val: LWWReg::default(),
            tombstone: LWWReg::default()
        });

        assert_eq!(m.get(&0), Some(&LWWReg { val: 0, dot: 0 }));
    }

    #[test]
    fn test_insert() {
        let mut m: Map<u16, LWWReg<u16, u16>, String> = Map::new();
        m.insert(32, LWWReg::default(), "a1".into());
        assert_eq!(m.get(&32), Some(&LWWReg { val: 0, dot: 0 }));
        assert_eq!(m.len(), 1);
    }

    #[test]
    fn test_update() {
        let mut m: Map<String, LWWReg<u16, u16>, String> = Map::new();

        // constructs a default value if reg does not exist
        m.update(
            "x".into(),
            |mut reg| {
                assert_eq!(reg, LWWReg::default());
                let new_val = (reg.val + 1) * 2;
                let new_dot = reg.dot + 1;
                assert!(reg.update(new_val, new_dot).is_ok());
                Some(reg)
            },
            "actor 1".into()
        );
        assert_eq!(m.get(&"x".into()), Some(&LWWReg { val: 2, dot: 1 }));

        // Updating once more should give the closure the updated LWWReg
        m.update(
            "x".into(),
            |mut reg| {
                assert_eq!(reg, LWWReg { val: 2, dot: 1 });
                let new_val = (reg.val + 1) * 2;
                let new_dot = reg.dot + 1;
                assert!(reg.update(new_val, new_dot).is_ok());
                Some(reg)
            },
            "actor 1".into()
        );
        
        assert_eq!(m.get(&"x".into()), Some(&LWWReg { val: 6, dot: 2 }));

        // Returning None from the closure should remove the element
        m.update(
            "x".into(),
            |reg| {
                assert_eq!(reg, LWWReg { val: 6, dot: 2 });
                None
            },
            "actor 1".into()
        );
        
        assert_eq!(m.get(&"x".into()), None);
    }

    #[test]
    fn test_remove() {
        let mut m: Map<String, LWWReg<u16, u16>, String> = Map::new();
        
        m.insert("x".into(), LWWReg { val: 6, dot: 2 }, "actor 1".into());
        assert_eq!(m.get(&"x".into()), Some(&LWWReg { val: 6, dot: 2 }));

        m.remove("x".into(), "actor 2".into());
    }

    #[test]
    fn test_reset_remove_semantics() {
        let mut m: Map<String, Orswot<u8, String>, String> = Map::new();
        m.update(
            "x".into(),
            |mut x_set| {
                x_set.add(57, "actor_1".into());
                Some(x_set)
            },
            "actor_1".into()
        );

        let mut m2 = m.clone();

        m.remove("x".into(), "actor_1".into());

        m2.update(
            "x".into(),
            |mut x_set| {
                x_set.add(21, "actor_2".into());
                Some(x_set)
            },
            "actor_2".into()
        );

        println!("m1 {:?}", m);
        println!("m2 {:?}", m2);
        let m_snapshot = m.clone();
        assert!(m.merge(&m2).is_ok());
        assert!(m2.merge(&m_snapshot).is_ok());

        assert_eq!(m, m2);

        let x_set = m.get(&"x".into()).unwrap();
        assert_eq!(x_set.value(), vec![21]);
    }

    #[test]
    fn test_inserts_with_non_descendent_clocks_are_noops() {
        let mut m: Map<u8, LWWReg<u8, u8>, u8> = Map::new();
        m.insert_with_ctx(0, LWWReg { val: 0, dot: 0 }, VClock::new());
        assert_eq!(m, Map::new());
    }

    #[test]
    fn test_remove_with_non_descendent_clocks_should_be_discarded() {
        let mut m: Map<u8, LWWReg<u8, u8>, u8> = Map::new();
        let mut ctx = VClock::new();
        ctx.witness(1, 23).unwrap();

        m.remove_with_ctx(0, ctx.clone());
        assert_ne!(m, Map::new()); // the remove should be stored as deferred
        let m_snapshot = m.clone();
        m.remove_with_ctx(0, ctx.clone()); // should be a no-op

        assert_eq!(m, m_snapshot);
    }

    #[test]
    fn test_removing_with_concurrent_clocks_should_keep_both_deferred_removes() {
        let mut m: Map<u8, LWWReg<u8, u8>, u8> = Map::new();

        let mut clock1 = VClock::new();
        let mut clock2 = VClock::new();
        clock1.witness(2, 6).unwrap();
        clock2.witness(1, 2).unwrap();

        m.remove_with_ctx(0, clock1.clone());
        m.remove_with_ctx(0, clock2.clone());

        assert_eq!(m.deferred.len(), 2);
    }

    #[test]
    fn test_ancester_updates_should_be_no_ops() {
        let mut m: Map<u8, LWWReg<u8, u8>, u8> = Map::new();

        let mut clock1 = VClock::new();
        let mut clock2 = VClock::new();
        clock1.witness(2, 6).unwrap();
        clock2.witness(2, 5).unwrap();

        m.insert_with_ctx(0, LWWReg::default(), clock1);
        let m_snapshot = m.clone();
        m.update_with_ctx(0, |_| None, clock2);

        assert_eq!(m, m_snapshot);
    }

    #[test]
    fn test_dunno() {
        // ([Remove(0, VClock { dots: {3: 6} })], [Remove(1, VClock { dots: {3: 6} })])
//        let mut clock1 = VClock::new();
//        let mut clock2 = VClock::new();
//        clock1.witness(2, 5).unwrap();
//        clock2.witness(2, 3).unwrap();
//        let ops1 = vec![Op::Insert(0, (0, 0, 0), clock1)];
//        let ops2 = vec![Op::Insert(1, (0, 0, 0), clock2)];
//
//        let mut m1 = Map::new();
//        let mut m2 = Map::new();
//
//        apply_ops(&mut m1, &ops1);
//        apply_ops(&mut m2, &ops2);
//        
//        apply_ops(&mut m1, &ops2);
//        apply_ops(&mut m2, &ops1);
//
//        assert_eq!(m1, m2);
    }
    
    fn test_ops() {
        // ([Insert(0, (0, 0, 0), VClock { dots: {1: 5} })], [Remove(0, VClock { dots: {1: 4} })])
        let ops1 = vec![];
        let ops2 = vec![];

        let mut m1 = Map::new();
        let mut m2 = Map::new();

        apply_ops(&mut m1, &ops1);
        apply_ops(&mut m2, &ops2);
        
        apply_ops(&mut m1, &ops2);
        apply_ops(&mut m2, &ops1);

        assert_eq!(m1, m2);
    }

    fn apply_ops(map: &mut Map<u8, LWWReg<u8, (u64, u16)>, u16>, ops: &[Op]) {
        for op in ops.iter() {
            op.apply(map);
        }
    }

    quickcheck! {
        fn prop_associativity_ops(ops1: Vec<Op>, ops2: Vec<Op>, ops3: Vec<Op>) -> bool {
            let mut m1 = Map::new();
            let mut m2 = Map::new();
            let mut m3 = Map::new();

            apply_ops(&mut m1, &ops1);
            apply_ops(&mut m2, &ops2);
            apply_ops(&mut m3, &ops3);

            let mut m1_snapshot = m1.clone();

            // (m1 ^ m2) ^ m3
            assert!(m1.merge(&m2).is_ok());
            assert!(m1.merge(&m3).is_ok());

            // m1 ^ (m2 ^ m3)
            assert!(m2.merge(&m3).is_ok());
            assert!(m1_snapshot.merge(&m2).is_ok());
            
            // (m1 ^ m2) ^ m3 = m1 ^ (m2 ^ m3)
            m1 == m1_snapshot
        }
        
        fn prop_commutativity_ops(ops1: Vec<Op>, ops2: Vec<Op>) -> bool {
            let mut m1 = Map::new();
            let mut m2 = Map::new();
            
            apply_ops(&mut m1, &ops1);
            apply_ops(&mut m2, &ops2);
            
            // m1 ^ m2
            assert!(m1.merge(&m2).is_ok());

            // m2 ^ m1
            assert!(m2.merge(&m1).is_ok());

            // m1 ^ m2 = m2 ^ m1
            m1 == m2
        }

        fn prop_idempotency(ops: Vec<Op>) -> bool {
            let mut m = Map::new();
            apply_ops(&mut m, &ops);
            let m_snapshot = m.clone();

            // m ^ m
            assert!(m.merge(&m_snapshot).is_ok());

            // m ^ m = m
            m == m_snapshot
        }

        fn prop_repeated_merge(op_pairs: Vec<(Op, Op)>, skip_merge: u8) -> bool {
            let mut m1 = Map::new();
            let mut m2 = Map::new();

            let mut merge_count = skip_merge;
            for (op1, op2) in op_pairs.iter() {
                op1.apply(&mut m1);
                op2.apply(&mut m2);
                if merge_count == 0 {
                    merge_count = skip_merge;
                    assert!(m1.merge(&m2).is_ok());
                    assert!(m2.merge(&m1).is_ok());
                    if m1 != m2 { return false }
                } else {
                    merge_count -= 1;
                }
            }

            assert!(m1.merge(&m2).is_ok());
            assert!(m2.merge(&m1).is_ok());

            m1 == m2
        }
//
//        fn prop_ops_commute(ops1: Vec<Op>, ops2: Vec<Op>) -> TestResult {
//            for op1 in ops1.iter() {
//                for op2 in ops2.iter() {
//                    let violation = match (op1, op2) {
//                        (Op::Remove(k1, c1), Op::Remove(k2, c2)) => c1 == c2 &&  k1 != k2,
//                        (Op::Insert(k1, v1, c1), Op::Insert(k2, v2, c2)) => c1 == c2 && (k1 != k2 || v1 != v2),
//                        (Op::Update(k1, v1, c1), Op::Update(k2, v2, c2)) => c1 == c2 && (k1 != k2 || v1 != v2),
//                        (Op::Remove(_, c1), Op::Insert(_, _, c2)) => c1 == c2,
//                        (Op::Remove(_, c1), Op::Update(_, _, c2)) => c1 == c2,
//                        (Op::Insert(_, _, c1), Op::Remove(_, c2)) => c1 == c2,
//                        (Op::Update(_, _, c1), Op::Remove(_, c2)) => c1 == c2,
//                        _ => false
//                    };
//                    if violation {
//                        return TestResult::discard();
//                    }
//                }
//            }
//            let mut m1 = Box::new(Map::new());
//            let mut m2 = Box::new(Map::new());
//
//            apply_ops(&mut m1, &ops1);
//            apply_ops(&mut m2, &ops2);
//            
//            apply_ops(&mut m1, &ops2);
//            apply_ops(&mut m2, &ops1);
//
//            TestResult::from_bool(m1 == m2)
//        }
    }
}
