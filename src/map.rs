use serde::Serialize;
use serde::de::DeserializeOwned;

use error::Result;
use traits::ComposableCrdt;
use vclock::VClock;
use std::collections::BTreeMap;

/// The Map CRDT allows for composition of CRDT's
#[derive(Debug, Clone, PartialEq)]
pub struct Map<K, V, A> where
    K: Ord + Clone + Serialize + DeserializeOwned,
    V: Clone + Serialize + DeserializeOwned + ComposableCrdt<A>,
    A: Ord + Clone + Serialize + DeserializeOwned
{
    clock: VClock<A>,
    entries: BTreeMap<K, MapEntry<V, A>>
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
        for (key, entry) in other.entries.iter() {
            // TODO(david) see about avoiding this remove here with entries.get_mut
            if let Some(mut existing_entry) = self.entries.remove(&key) {
                existing_entry.clock.merge(&entry.clock);
                existing_entry.val.merge(&entry.val)?;
                existing_entry.tombstone.merge(&entry.tombstone)?;
                existing_entry.val.merge(&existing_entry.tombstone)?;
                self.entries.insert(key.clone(), existing_entry);
            } else {
                // we don't have this entry, is this because we removed it? or is it new
                if self.clock >= entry.clock {
                    // we removed this entry! don't add it back!
                } else {
                    // this is either a new entry from other, or an entry we removed but
                    // other has concurrently mutated.
                    let mut clock = entry.clock.clone();
                    let mut tombstone = V::default();
                    tombstone.set_clock(self.clock.clone());
                    let mut val = entry.val.clone();
                    val.merge(&tombstone)?;
                    self.entries.insert(key.clone(), MapEntry { clock, val, tombstone });
                }
            }
        }

        // check for entries that we have but are missing in the other
        let mut to_remove = Vec::new();
        for (key, mut entry) in self.entries.iter_mut() {
            if other.entries.get(&key).is_none() {
                if other.clock >= entry.clock {
                    // the other has seen this entry and removed it
                    to_remove.push(key.clone());
                } else if other.clock.concurrent(&entry.clock) {
                    // the other has removed this entry but we have modified it as well
                    entry.tombstone.set_clock(other.clock.clone());
                    entry.val.merge(&entry.tombstone)?;
                }
            }
        }

        for key in to_remove.into_iter() {
            self.entries.remove(&key);
        }

        self.clock.merge(&other.clock);
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
            entries: BTreeMap::new()
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

    /// !! `insert()` destroy causality! think of it as the equivalent of removing and adding a new element.
    ///       if you want to update a crdt while preserving causal history, consider using `update()`.
    pub fn insert(&mut self, key: K, val: V, actor: A) {
        let actor_version = self.clock.increment(actor.clone());
        let mut tombstone = V::default();
        tombstone.set_clock(self.clock.clone());
        let mut dot = VClock::new();
        // this witness should never fail because dot is brand new
        dot.witness(actor, actor_version).unwrap();

        self.entries.insert(key, MapEntry { clock: dot, val, tombstone });
    }

    /// hehe
    pub fn update<F>(&mut self, key: K, mut updater: F,actor: A) where
        F: FnMut(V) -> Option<V>
    {
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


    /// Remove a key from the Map
    pub fn remove(&mut self, key: K, actor: A) {
        self.clock.increment(actor.clone());

        if let Some(map_entry) = self.entries.remove(&key) {
            if !(self.clock >= map_entry.clock) {
                panic!("map's clock is lower than the entries clock")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    use lwwreg::LWWReg;
    use orswot::Orswot;

    use quickcheck::{Arbitrary, Gen};


    #[derive(Debug, Clone, PartialEq)]
    enum Op {
        Rm(u8),
        Put(u8, (u8, u64, u16)),
        Up(u8, Option<(u8, u64, u16)>),
    }

    impl Op {
        fn apply(&self, map: &mut Map<u8, LWWReg<u8, (u64, u16)>, u16>, actor: u16) {
            match self.clone() {
                Op::Rm(key) => {
                    map.remove(key, actor);
                },
                Op::Put(key, (val, time, lww_actor)) => {
                    map.insert(key, LWWReg { val: val, dot: (time, lww_actor) }, actor);
                },
                Op::Up(key, None) => {
                    map.update(key, |_| None, actor);
                }
                Op::Up(key, Some((val, dot, lww_actor))) => {
                    map.update(key, |mut reg| {
                        reg.update(val, (dot, lww_actor)).unwrap();
                        Some(reg)
                    }, actor);
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

            let choices = [
                Op::Rm(key),
                Op::Put(key, (val, time, actor)),
                Op::Up(key, *(g.choose(&[None, Some((val, time, actor))]).unwrap()))
            ];
            let op = g.choose(&choices).unwrap();
            op.clone()
        }

        fn shrink(&self) -> Box<Iterator<Item = Op>> {
            let vec: Vec<Op> = match self.clone() {
                Op::Rm(key) => 
                    vec![Op::Rm(key/2)],
                Op::Put(key, (val, time, actor)) =>
                    vec![Op::Put(key/2, (val, time, actor)),
                         Op::Put(key,   (val/2, time, actor)),
                         Op::Put(key,   (val, time/2, actor)),
                         Op::Put(key,   (val, time, actor/2))],
                Op::Up(key, None) =>
                    vec![Op::Up(key/2, None),
                         Op::Rm(key)],
                Op::Up(key, Some((val, time, actor))) =>
                    vec![Op::Up(key/2, Some((val, time, actor))),
                         Op::Up(key,   Some((val/2, time, actor))),
                         Op::Up(key,   Some((val, time/2, actor))),
                         Op::Up(key,   Some((val, time, actor/2))),
                         Op::Up(key,   None)]
            };
            let self_snapshot = self.clone();
            Box::new(
                vec.into_iter()
                    .filter(move |op| op != &self_snapshot)
            )
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
        let mut m1: Map<String, Orswot<u8, String>, String> = Map::new();
        m1.update(
            "x".into(),
            |mut x_set| {
                x_set.add(1, "a1".into());
                Some(x_set)
            },
            "a1".into()
        );

        let mut m2 = m1.clone();

        m1.remove("x".into(), "a1".into());

        m2.update(
            "x".into(),
            |mut x_set| {
                x_set.add(2, "a2".into());
                Some(x_set)
            },
            "a2".into()
        );

        println!("m1 {:?}", m1);
        println!("m2 {:?}", m2);
        let m1_snapshot = m1.clone();
        assert!(m1.merge(&m2).is_ok());
        assert!(m2.merge(&m1_snapshot).is_ok());

        println!("m1 {:?}", m1);
        println!("m2 {:?}", m2);
        
        assert_eq!(m1, m2);

        let x_set = m1.get(&"x".into()).unwrap();
        assert_eq!(x_set.value(), vec![2]);
    }

    fn apply_ops(map: &mut Map<u8, LWWReg<u8, (u64, u16)>, u16>, ops: &[Op], actor: u16) {
        for op in ops.iter() {
            op.apply(map, actor);
        }
    }

    quickcheck! {
        fn prop_associativity_ops(ops1: Vec<Op>, ops2: Vec<Op>, ops3: Vec<Op>) -> bool {
            let mut m1 = Map::new();
            let mut m2 = Map::new();
            let mut m3 = Map::new();

            apply_ops(&mut m1, &ops1, 1);
            apply_ops(&mut m2, &ops2, 2);
            apply_ops(&mut m3, &ops3, 3);

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
            
            apply_ops(&mut m1, &ops1, 1);
            apply_ops(&mut m2, &ops2, 2);
            
            // m1 ^ m2
            assert!(m1.merge(&m2).is_ok());

            // m2 ^ m1
            assert!(m2.merge(&m1).is_ok());

            // m1 ^ m2 = m2 ^ m1
            m1 == m2
        }

        fn prop_idempotency(ops: Vec<Op>) -> bool {
            let mut m = Map::new();
            apply_ops(&mut m, &ops, 1);
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
                op1.apply(&mut m1, 1);
                op2.apply(&mut m2, 2);
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
    }
}
