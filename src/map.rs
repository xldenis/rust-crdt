use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Debug;

use serde::Serialize;
use serde::de::DeserializeOwned;

use traits::{Causal, CvRDT, CmRDT};
use vclock::{Dot, VClock, Actor};
use ctx::{ReadCtx, AddCtx, RmCtx};

/// Key Trait alias to reduce redundancy in type decl.
pub trait Key: Debug + Ord + Clone + Send + Serialize + DeserializeOwned {}
impl<T: Debug + Ord + Clone + Send + Serialize + DeserializeOwned> Key for T {}

/// Val Trait alias to reduce redundancy in type decl.
pub trait Val<A: Actor>
    : Debug + Default + Clone + Send + Serialize + DeserializeOwned
    + Causal<A> + CmRDT + CvRDT
{}

impl<A, T> Val<A> for T where
    A: Actor,
    T: Debug + Default + Clone + Send + Serialize + DeserializeOwned
    + Causal<A> + CmRDT + CvRDT
{}

/// Map CRDT - Supports Composition of CRDT's with reset-remove semantics.
///
/// Reset-remove means that if one replica removes an entry while another
/// actor concurrently edits that entry, once we sync these two maps, we
/// will see that the entry is still in the map but all edits seen by the
/// removing actor will be gone. To understand this more clearly see the
/// following example:
///
/// ``` rust
/// use crdts::{Map, Orswot, CvRDT, CmRDT};
///
/// type Actor = u64;
/// type Friend = String;
///
/// let mut friends: Map<Friend, Orswot<Friend, Actor>, Actor> = Map::new();
/// let a1 = 10837103590u64; // initial actors id
///
/// let op = friends.update(
///     "alice",
///     friends.get(&"alice".to_string()).derive_add_ctx(a1),
///     |set, ctx| set.add("bob", ctx)
/// );
/// friends.apply(&op);
///
/// let mut friends_replica = friends.clone();
/// let a2 = 8947212u64; // the replica's actor id
///
/// // now the two maps diverge. the original map will remove "alice" from the map
/// // while the replica map will update the "alice" friend set to include "clyde".
///
/// let rm_op = friends.rm("alice", friends.get(&"alice".to_string()).derive_rm_ctx());
/// friends.apply(&rm_op);
///
/// let replica_op = friends_replica.update(
///     "alice",
///     friends_replica.get(&"alice".into()).derive_add_ctx(a2),
///     |set, ctx| set.add("clyde", ctx)
/// );
/// friends_replica.apply(&replica_op);
///
/// assert_eq!(friends.get(&"alice".into()).val, None);
/// assert_eq!(
///     friends_replica.get(&"alice".into()).val.map(|set| set.value().val),
///     Some(vec!["bob".to_string(), "clyde".to_string()])
/// );
///
/// // On merge, we should see "alice" in the map but her friend set should only have "clyde".
///
/// friends.merge(&friends_replica);
///
/// let alice_friends = friends.get(&"alice".into()).val
///     .map(|set| set.value().val);
/// assert_eq!(alice_friends, Some(vec!["clyde".into()]));
/// ```
#[serde(bound(deserialize = ""))]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Map<K: Key, V: Val<A>, A: Actor> {
    // This clock stores the current version of the Map, it should
    // be greator or equal to all Entry.clock's in the Map.
    clock: VClock<A>,
    entries: BTreeMap<K, Entry<V, A>>,
    deferred: HashMap<VClock<A>, BTreeSet<K>>
}

#[serde(bound(deserialize = ""))]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
struct Entry<V: Val<A>, A: Actor> {
    // The entry clock tells us which actors edited this entry.
    clock: VClock<A>,

    // The nested CRDT
    val: V
}

/// Operations which can be applied to the Map CRDT
#[serde(bound(deserialize = ""))]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Op<K: Key, V: Val<A>, A: Actor> {
    /// No change to the CRDT
    Nop,
    /// Remove a key from the map
    Rm {
        /// The clock under which we will perform this remove
        clock: VClock<A>,
        /// Key to remove
        key: K
    },
    /// Update an entry in the map
    Up {
        /// Actors version at the time of the update
        dot: Dot<A>,
        /// Key of the value to update
        key: K,
        /// The operation to apply on the value under `key`
        op: V::Op
    }
}

impl<K: Key, V: Val<A>, A: Actor> Default for Map<K, V, A> {
    fn default() -> Self {
        Map::new()
    }
}

impl<K: Key, V: Val<A>, A: Actor> Causal<A> for Map<K, V, A> {
    fn truncate(&mut self, clock: &VClock<A>) {
        let mut to_remove: Vec<K> = Vec::new();
        for (key, entry) in self.entries.iter_mut() {
            entry.clock.subtract(&clock);
            if entry.clock.is_empty() {
                to_remove.push(key.clone());
            } else {
                entry.val.truncate(&clock);
            }
        }

        for key in to_remove {
            self.entries.remove(&key);
        }

        let mut deferred = HashMap::new();
        for (rm_clock, key) in self.deferred.iter() {
            let surviving_dots = rm_clock.dominating_vclock(&clock);
            if !surviving_dots.is_empty() {
                deferred.insert(surviving_dots, key.clone());
            }
        }
        self.deferred = deferred;

        self.clock.subtract(&clock);
    }
}

impl<K: Key, V: Val<A>, A: Actor> CmRDT for Map<K, V, A> {
    type Op = Op<K, V, A>;

    fn apply(&mut self, op: &Self::Op) {
        match op.clone() {
            Op::Nop => {/* do nothing */},
            Op::Rm { clock, key } => {
                self.apply_rm(key, &clock);
            },
            Op::Up { dot: Dot { actor, counter }, key, op } => {
                if self.clock.get(&actor) >= counter {
                    // we've seen this op already
                    return;
                }

                let mut entry = self.entries.remove(&key)
                    .unwrap_or_else(|| Entry {
                        clock: VClock::new(),
                        val: V::default()
                    });

                entry.clock.witness(actor.clone(), counter).unwrap();
                entry.val.apply(&op);
                self.entries.insert(key.clone(), entry);

                self.clock.witness(actor, counter).unwrap();
                self.apply_deferred();
            }
        }
    }
}

impl<K: Key, V: Val<A>, A: Actor> CvRDT for Map<K, V, A> {
    fn merge(&mut self, other: &Self) {
        let mut other_remaining = other.entries.clone();
        let mut keep = BTreeMap::new();
        for (key, mut entry) in self.entries.clone().into_iter() {
            match other.entries.get(&key) {
                None => {
                    // other doesn't contain this entry because it:
                    //  1. has witnessed it and dropped it
                    //  2. hasn't witnessed it
                    let dom_clock = entry.clock.dominating_vclock(&other.clock);
                    if dom_clock.is_empty() {
                        // the other map has witnessed the entry's clock, and dropped this entry
                    } else {
                        // the other map has not witnessed this add, so add it
                        let dots_that_this_entry_should_not_have = other.clock.dominating_vclock(&dom_clock);
                        entry.val.truncate(&dots_that_this_entry_should_not_have);
                        entry.clock = dom_clock;
                        keep.insert(key, entry);
                    }
                }
                Some(other_entry) => {
                    // SUBTLE: this entry is present in both orswots, BUT that doesn't mean we
                    // shouldn't drop it!
                    let common = entry.clock.intersection(&other_entry.clock);
                    let luniq = entry.clock.dominating_vclock(&common);
                    let runiq = other_entry.clock.dominating_vclock(&common);
                    let lkeep = luniq.dominating_vclock(&other.clock);
                    let rkeep = runiq.dominating_vclock(&self.clock);
                    // Perfectly possible that an item in both sets should be dropped
                    let mut common = common;
                    common.merge(&lkeep);
                    common.merge(&rkeep);
                    if !common.is_empty() {
                        // we should not drop, as there are common clocks
                        entry.val.merge(&other_entry.val);
                        let mut merged_clocks = entry.clock.clone();
                        merged_clocks.merge(&other_entry.clock);
                        let dots_that_this_entry_should_not_have = merged_clocks.dominating_vclock(&common);
                        entry.val.truncate(&dots_that_this_entry_should_not_have);
                        entry.clock = common;
                        keep.insert(key.clone(), entry);
                    }
                    // don't want to consider this again below
                    other_remaining.remove(&key).unwrap();
                }
            }
        }

        for (key, mut entry) in other_remaining.into_iter() {
            let dom_clock = entry.clock.dominating_vclock(&self.clock);
            if !dom_clock.is_empty() {
                // other has witnessed a novel addition, so add it
                let dots_that_this_entry_should_not_have = self.clock.dominating_vclock(&dom_clock);
                entry.val.truncate(&dots_that_this_entry_should_not_have);
                entry.clock = dom_clock;
                keep.insert(key, entry);
            }
        }

        // merge deferred removals
        for (clock, deferred) in other.deferred.iter() {
            for key in deferred {
                self.apply_rm(key.clone(), &clock);
            }
        }

        self.entries = keep;

        // merge vclocks
        self.clock.merge(&other.clock);

        self.apply_deferred();
    }
}

impl<K: Key, V: Val<A>, A: Actor> Map<K, V, A> {
    /// Constructs an empty Map
    pub fn new() -> Map<K, V, A> {
        Map {
            clock: VClock::new(),
            entries: BTreeMap::new(),
            deferred: HashMap::new()
         }
    }

    /// Returns the number of entries in the Map
    pub fn len(&self) -> ReadCtx<usize, A> {
        ReadCtx {
            add_clock: self.clock.clone(),
            rm_clock: self.clock.clone(),
            val: self.entries.len()
        }
    }

    /// Retrieve value stored under a key
    pub fn get(&self, key: &K) -> ReadCtx<Option<V>, A> {
        let add_clock = self.clock.clone();
        let entry_opt = self.entries.get(&key);
        ReadCtx {
            add_clock: add_clock,
            rm_clock: entry_opt
                .map(|map_entry| map_entry.clock.clone())
                .unwrap_or_else(|| VClock::new()),
            val: entry_opt
                .map(|map_entry| map_entry.val.clone())
        }
    }

    /// Update a value under some key, if the key is not present in the map,
    /// the updater will be given the result of V::default().
    pub fn update<F, I>(&self, key: I, ctx: AddCtx<A>, f: F) -> Op<K, V, A>
        where F: FnOnce(&V, AddCtx<A>) -> V::Op,
              I: Into<K>
    {
        let key = key.into();
        let op = if let Some(entry) = self.entries.get(&key) {
            f(&entry.val, ctx.clone())
        } else {
            f(&V::default(), ctx.clone())
        };
        Op::Up { dot: ctx.dot, key, op }
    }

    /// Remove an entry from the Map
    pub fn rm(&self, key: impl Into<K>, ctx: RmCtx<A>) -> Op<K, V, A> {
        Op::Rm { clock: ctx.clock, key: key.into() }
    }

    /// apply the pending deferred removes 
    fn apply_deferred(&mut self) {
        let deferred = self.deferred.clone();
        self.deferred = HashMap::new();
        for (clock, keys) in deferred {
            for key in keys {
                self.apply_rm(key, &clock);
            }
        }
    }

    /// Apply a key removal given a clock.
    fn apply_rm(&mut self, key: K, clock: &VClock<A>) {
        if !clock.dominating_vclock(&self.clock).is_empty() {
            let deferred_set = self.deferred.entry(clock.clone())
                .or_insert_with(|| BTreeSet::new());
            deferred_set.insert(key.clone());
        }

        if let Some(mut existing_entry) = self.entries.remove(&key) {
            let dom_clock = existing_entry.clock.dominating_vclock(&clock);
            if !dom_clock.is_empty() {
                existing_entry.clock = dom_clock;
                existing_entry.val.truncate(&clock);
                self.entries.insert(key.clone(), existing_entry);
            }
        }
    }

}

#[cfg(test)]
mod tests {
    use super::*;

    use quickcheck::{Arbitrary, Gen, TestResult};

    use mvreg::{self, MVReg};

    type TestActor = u8;
    type TestKey = u8;
    type TestVal = MVReg<u8, TestActor>;
    type TestOp = Op<TestKey, Map<TestKey, TestVal, TestActor>, TestActor>;
    type TestMap =  Map<TestKey, Map<TestKey, TestVal, TestActor>, TestActor>;

    #[derive(Debug, Clone)]
    struct OpVec(TestActor, Vec<TestOp>);

    impl<K, V, A> Arbitrary for Op<K, V, A> where
        K: Key + Arbitrary,
        V: Val<A> + Arbitrary,
        A: Actor + Arbitrary,
        V::Op: Arbitrary
    {
        fn arbitrary<G: Gen>(_g: &mut G) -> Self {
            /// we don't generate arbitrary Op's in isolation
            /// since they are highly likely to conflict with
            /// other ops, insted we generate OpVec's.
            unimplemented!();
        }

        fn shrink(&self) -> Box<Iterator<Item = Op<K, V, A>>> {
            let mut shrunk: Vec<Op<K, V, A>> = Vec::new();

            match self.clone() {
                Op::Nop => {/* shrink to nothing */},
                Op::Rm { clock, key } => {
                    shrunk.extend(
                        clock.shrink()
                            .map(|c| Op::Rm {
                                clock: c,
                                key: key.clone()
                            })
                            .collect::<Vec<Self>>()
                    );

                    shrunk.extend(
                        key.shrink()
                            .map(|k| Op::Rm {
                                clock: clock.clone(),
                                key: k.clone()
                            }).collect::<Vec<Self>>()
                    );

                    shrunk.push(Op::Nop);
                },
                Op::Up { dot, key, op } => {
                    shrunk.extend(
                        key.shrink()
                            .map(|k| Op::Up {
                                dot: dot.clone(),
                                key: k,
                                op: op.clone() })
                            .collect::<Vec<Self>>()
                    );
                    shrunk.extend(
                        op.shrink()
                            .map(|o| Op::Up {
                                dot: dot.clone(),
                                key: key.clone(),
                                op: o
                            })
                            .collect::<Vec<Self>>()
                    );
                    shrunk.push(Op::Nop);
                }
            }

            Box::new(shrunk.into_iter())
        }
    }

    impl Arbitrary for Map<TestKey, TestVal, TestActor> {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            let mut map: Map<TestKey, TestVal, TestActor> = Map::new();
            let num_entries: u8 = g.gen_range(0, 30);
            for _ in 0..num_entries {
                let key: u8 = g.gen();
                let actor = g.gen_range(0, 10);
                let coin_toss = g.gen();
                let ctx = map.get(&key);
                let reg_val: u8 = g.gen();
                let op = match coin_toss {
                    true =>
                        map.update(key, ctx.derive_add_ctx(actor), |r, ctx| r.set(reg_val, ctx)
                        ),
                    false =>
                        map.rm(key, ctx.derive_rm_ctx())
                };
                map.apply(&op);
            }
            map
        }

        fn shrink(&self) -> Box<Iterator<Item = Self>> {
            let mut shrunk = Vec::new();
            for dot in self.clock.clone().into_iter() {
                let mut map = self.clone();
                let clock: VClock<u8> = self.clock.clone()
                    .into_iter()
                    .filter(|d| d != &dot)
                    .collect();
                map.truncate(&clock);
                shrunk.push(map);
            }

            for key in self.entries.keys() {
                let mut map = self.clone();
                map.entries.remove(&key);
                shrunk.push(map);
            }

            for (key, entry) in self.entries.iter() {
                for clock in entry.clock.shrink().filter(|c| !c.is_empty()) {
                    let mut map = self.clone();
                    let mut shrunk_entry = entry.clone();
                    shrunk_entry.val.truncate(&clock);
                    shrunk_entry.clock = clock;
                    map.entries.insert(key.clone(), shrunk_entry);
                    shrunk.push(map)
                }
            }

            Box::new(shrunk.into_iter())
        }
    }

    impl Arbitrary for OpVec {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            let actor = TestActor::arbitrary(g);
            let num_ops: u8 = g.gen_range(0, 50);
            let mut ops = Vec::with_capacity(num_ops as usize);
            for i in 0..num_ops {
                let die_roll: u8 = g.gen();
                let die_roll_inner: u8 = g.gen();
                let clock: VClock<_> = Dot { actor, counter: i as u64 }.into();

                let op = match die_roll % 3 {
                    0 => {
                        let dot = Dot { actor, counter: clock.get(&actor) };
                        Op::Up {
                            dot: dot.clone(),
                            key: g.gen(),
                            op: match die_roll_inner % 3 {
                                0 => Op::Up {
                                    dot: dot.clone(),
                                    key: g.gen(),
                                    op: mvreg::Op::Put {
                                        clock,
                                        val: g.gen()
                                    }
                                },
                                1 => Op::Rm {
                                    clock: clock,
                                    key: g.gen()
                                },
                                _ => Op::Nop
                            }
                        }
                    },
                    1 => Op::Rm { clock, key: g.gen() },
                    _ => Op::Nop
                };
                ops.push(op);
            }
            OpVec(actor, ops)
        }

        fn shrink(&self) -> Box<Iterator<Item = Self>> {
            let mut shrunk: Vec<Self> = Vec::new();
            for i in 0..self.1.len() {
                let mut vec = self.1.clone();
                vec.remove(i);
                shrunk.push(OpVec(self.0.clone(), vec))
            }
            
            Box::new(shrunk.into_iter())
        }
    }
    
    #[test]
    fn test_new() {
        let m: TestMap = Map::new();
        assert_eq!(m.len().val, 0);
    }
    
    #[test]
    fn test_get() {
        let mut m: TestMap = Map::new();
        
        assert_eq!(m.get(&0).val, None);
        
        let op_1 = m.clock.inc(1);
        m.clock.apply(&op_1);
        
        m.entries.insert(0, Entry {
            clock: m.clock.clone(),
            val: Map::default()
        });

        assert_eq!(m.get(&0).val, Some(Map::new()));
    }
    
    #[test]
    fn test_update() {
        let mut m: TestMap = Map::new();
        
        // constructs a default value if does not exist
        let ctx = m.get(&101).derive_add_ctx(1);
        let op = m.update(101, ctx, |map, ctx| {
            map.update(110, ctx, |reg, ctx| reg.set(2, ctx))
        });
        
        assert_eq!(
            op,
            Op::Up {
                dot: Dot { actor: 1, counter: 1 },
                key: 101,
                op: Op::Up {
                    dot: Dot { actor: 1, counter: 1 },
                    key: 110,
                    op: mvreg::Op::Put {
                        clock: Dot { actor: 1, counter: 1 }.into(),
                        val: 2
                    }
                }
            }
        );
        
        assert_eq!(m, Map::new());
        
        m.apply(&op);
        
        assert_eq!(
            m.get(&101).val
                .and_then(|m2| m2.get(&110).val)
                .map(|r| r.read().val),
            Some(vec![2])
        );
        
        // the map should give the latest val to the closure
        let op2 = m.update(101, m.get(&101).derive_add_ctx(1), |map, ctx| {
            map.update(110, ctx, |reg, ctx| {
                assert_eq!(reg.read().val, vec![2]);
                reg.set(6, ctx)
            })
        });
        m.apply(&op2);
        
        assert_eq!(
            m.get(&101).val
                .and_then(|m2| m2.get(&110).val)
                .map(|r| r.read().val),
            Some(vec![6])
        );
    }
    
    #[test]
    fn test_remove() {
        let mut m: TestMap = Map::new();
        let add_ctx = m.get(&101).derive_add_ctx(1);
        let op = m.update(
            101,
            add_ctx.clone(),
            |m, ctx| m.update(110, ctx, |r, ctx| r.set(0, ctx))
        );
        let mut inner_map: Map<TestKey, TestVal, TestActor> = Map::new();
        let inner_op = inner_map.update(110, add_ctx, |r, ctx| r.set(0, ctx));
        inner_map.apply(&inner_op);
        
        m.apply(&op);
        
        let rm_op = {
            let read_ctx = m.get(&101);
            assert_eq!(read_ctx.val, Some(inner_map));
            assert_eq!(m.len().val, 1);
            let rm_ctx = read_ctx.derive_rm_ctx();
            m.rm(101, rm_ctx)
        };
        m.apply(&rm_op);
        assert_eq!(m.get(&101).val, None);
        assert_eq!(m.len().val, 0);
    }
    
    #[test]
    fn test_reset_remove_semantics() {
        let mut m1 = TestMap::new();
        let op1 = m1.update(101, m1.get(&101).derive_add_ctx(74), |map, ctx| {
            map.update(110, ctx, |reg, ctx| {
                reg.set(32, ctx)
            })
        });
        m1.apply(&op1);
        
        let mut m2 = m1.clone();
        
        let read_ctx = m1.get(&101);
        
        let op2 = m1.rm(101, read_ctx.derive_rm_ctx());
        m1.apply(&op2);
        
        let op3 = m2.update(101, m2.get(&101).derive_add_ctx(37), |map, ctx| {
            map.update(220, ctx, |reg, ctx| {
                reg.set(5, ctx)
            })
        });
        m2.apply(&op3);
        
        let m1_snapshot = m1.clone();
        
        m1.merge(&m2);
        m2.merge(&m1_snapshot);
        assert_eq!(m1, m2);
        
        let inner_map = m1.get(&101).val.unwrap();
        assert_eq!(inner_map.get(&220).val.map(|r| r.read().val), Some(vec![5]));
        assert_eq!(inner_map.get(&110).val, None);
        assert_eq!(inner_map.len().val, 1);
    }
    
    #[test]
    fn test_updating_with_current_clock_should_be_a_nop() {
        let mut m1: TestMap = Map::new();
        
        m1.apply(&Op::Up {
            dot: Dot { actor: 1, counter: 0 },
            key: 0,
            op: Op::Up {
                dot: Dot { actor: 1, counter: 0 },
                key: 1,
                op: mvreg::Op::Put {
                    clock: VClock::new(),
                    val: 235
                }
            }
        });
        
        // the update should have been ignored
        assert_eq!(m1, Map::new());
    }
    
    #[test]
    fn test_concurrent_update_and_remove_add_bias() {
        let mut m1 = TestMap::new();
        let mut m2 = TestMap::new();
        
        let op1 = Op::Rm {
            clock: Dot { actor: 1, counter: 1 }.into(),
            key: 102
        };
        let op2 = m2.update(102, m2.get(&102).derive_add_ctx(2), |_, _| Op::Nop);
        
        m1.apply(&op1);
        m2.apply(&op2);
        
        let mut m1_clone = m1.clone();
        let mut m2_clone = m2.clone();
        
        m1_clone.merge(&m2);
        m2_clone.merge(&m1);
        
        assert_eq!(m1_clone, m2_clone);
        
        m1.apply(&op2);
        m2.apply(&op1);
        
        assert_eq!(m1, m2);
        
        assert_eq!(m1, m1_clone);
        
        // we bias towards adds
        assert!(m1.get(&102).val.is_some());
    }
    
    #[test]
    fn test_op_exchange_commutes_quickcheck1() {
        // THIS WILL NOT PASS IF WE SWAP OUT THE MVREG WITH AN LWWREG
        // we need a true causal register
        let mut m1: Map<u8, MVReg<u8, u8>, u8> = Map::new();
        let mut m2: Map<u8, MVReg<u8, u8>, u8> = Map::new();
        
        let m1_op1 = m1.update(0, m1.get(&0).derive_add_ctx(1), |reg, ctx| reg.set(0, ctx));
        m1.apply(&m1_op1);
        
        let m1_op2 = m1.rm(0, m1.get(&0).derive_rm_ctx());
        m1.apply(&m1_op2);
        
        let m2_op1 = m2.update(0, m2.get(&0).derive_add_ctx(2), |reg, ctx| reg.set(0, ctx));
        m2.apply(&m2_op1);
        
        // m1 <- m2
        m1.apply(&m2_op1);
        
        // m2 <- m1
        m2.apply(&m1_op1);
        m2.apply(&m1_op2);
        
        assert_eq!(m1, m2);
    }
    
    #[test]
    fn test_op_deferred_remove() {
        let mut m1: Map<u8, MVReg<u8, u8>, u8> = Map::new();
        let mut m2 = m1.clone();
        let mut m3 = m1.clone();
        
        let m1_up1 = m1.update(
            0,
            m1.get(&0).derive_add_ctx(1),
            |reg, ctx| reg.set(0, ctx)
        );
        m1.apply(&m1_up1);
        
        let m1_up2 = m1.update(
            1,
            m1.get(&1).derive_add_ctx(1),
            |reg, ctx| reg.set(1, ctx)
        );
        m1.apply(&m1_up2);
        
        m2.apply(&m1_up1);
        m2.apply(&m1_up2);
        
        let read_ctx = m2.get(&0);
        let m2_rm = m2.rm(0, read_ctx.derive_rm_ctx());
        m2.apply(&m2_rm);
        
        println!("{:#?}", m3);
        assert_eq!(m2.get(&0).val, None);
        m3.apply(&m2_rm);
        println!("{:#?}", m3);
        assert_eq!(m3.deferred.len(), 1);
        m3.apply(&m1_up1);
        println!("{:#?}", m3);
        assert_eq!(m3.deferred.len(), 0);
        m3.apply(&m1_up2);
        println!("{:#?}", m3);
        
        m1.apply(&m2_rm);
        
        assert_eq!(m2.get(&0).val, None);
        assert_eq!(
            m3.get(&1).val
                .map(|r| r.read().val),
            Some(vec![1])
        );
        
        assert_eq!(m2, m3);
        assert_eq!(m1, m2);
        assert_eq!(m1, m3);
    }
    
    #[test]
    fn test_merge_deferred_remove() {
        let mut m1 = TestMap::new();
        let mut m2 = TestMap::new();
        let mut m3 = TestMap::new();
        
        let m1_up1 = m1.update(
            0,
            m1.get(&0).derive_add_ctx(1),
            |map, ctx| map.update(0, ctx, |reg, ctx| {
                reg.set(0, ctx)
            })
        );
        m1.apply(&m1_up1);
        
        let m1_up2 = m1.update(
            1,
            m1.get(&1).derive_add_ctx(1),
            |map, ctx| map.update(1, ctx, |reg, ctx| {
                reg.set(1, ctx)
            })
        );
        m1.apply(&m1_up2);

        m2.apply(&m1_up1);
        m2.apply(&m1_up2);
        
        let m2_rm = m2.rm(0, m2.get(&0).derive_rm_ctx());
        m2.apply(&m2_rm);
        
        m3.merge(&m2);
        m3.merge(&m1);
        m1.merge(&m2);
        
        assert_eq!(m2.get(&0).val, None);
        assert_eq!(
            m3.get(&1).val
                .and_then(|inner| inner.get(&1).val)
                .map(|r| r.read().val),
            Some(vec![1])
        );
        
        assert_eq!(m2, m3);
        assert_eq!(m1, m2);
        assert_eq!(m1, m3);
    }
    
    #[test]
    fn test_commute_quickcheck_bug() {
        let ops = vec![
            Op::Rm {
                clock: Dot { actor: 45, counter: 1 }.into(),
                key: 0
            },
            Op::Up {
                dot: Dot { actor: 45, counter: 2 },
                key: 0,
                op: Op::Up {
                    dot: Dot { actor: 45, counter: 1 },
                    key: 0,
                    op: mvreg::Op::Put { clock: VClock::new(), val: 0 }
                }
            }
        ];
        
        let mut m = Map::new();
        apply_ops(&mut m, &ops);
        
        let m_snapshot = m.clone();
        
        let mut empty_m = Map::new();
        m.merge(&empty_m);
        empty_m.merge(&m_snapshot);
        
        assert_eq!(m, empty_m);
    }
    
    #[test]
    fn test_idempotent_quickcheck_bug1() {
        let ops = vec![
            Op::Up {
                dot: Dot { actor: 21, counter: 5 },
                key: 0,
                op: Op::Nop
            },
            Op::Up {
                dot: Dot { actor: 21, counter: 6 },
                key: 1,
                op: Op::Up {
                    dot: Dot { actor: 21, counter: 1 },
                    key: 0,
                    op: mvreg::Op::Put { clock: VClock::new(), val: 0 }
                }
            }
        ];
        
        let mut m = Map::new();
        apply_ops(&mut m, &ops);
        
        let m_snapshot = m.clone();
        m.merge(&m_snapshot);
        
        assert_eq!(m, m_snapshot);
    }
    
    #[test]
    fn test_idempotent_quickcheck_bug2() {
        let mut m: TestMap = Map::new();
        m.apply(&Op::Up {
            dot: Dot { actor: 32, counter: 5 },
            key: 0,
            op: Op::Up {
                dot: Dot { actor: 32, counter: 5 },
                key: 0,
                op: mvreg::Op::Put { clock: VClock::new(), val: 0 }
            }
        });
        
        let m_snapshot = m.clone();
        
        // m ^ m
        m.merge(&m_snapshot);
        
        // m ^ m = m
        assert_eq!(m, m_snapshot);
    }
    
    #[test]
    fn test_nop_on_new_map_should_remain_a_new_map() {
        let mut map = TestMap::new();
        map.apply(&Op::Nop);
        assert_eq!(map, TestMap::new());
    }
    
    #[test]
    fn test_op_exchange_same_as_merge_quickcheck1() {
        let op1 = Op::Up {
            dot: Dot { actor: 38, counter: 4 },
            key: 216,
            op: Op::Nop
        };
        let op2 = Op::Up {
            dot: Dot { actor: 91, counter: 9 },
            key: 216,
            op: Op::Up {
                dot: Dot { actor: 91, counter: 1 },
                key: 37,
                op: mvreg::Op::Put {
                    clock: Dot { actor: 91, counter: 1 }.into(),
                    val: 94
                }
            }
        };
        let mut m1: TestMap = Map::new();
        let mut m2: TestMap = Map::new();
        m1.apply(&op1);
        m2.apply(&op2);
        
        let mut m1_merge = m1.clone();
        m1_merge.merge(&m2);
        
        let mut m2_merge = m2.clone();
        m2_merge.merge(&m1);
        
        m1.apply(&op2);
        m2.apply(&op1);
        
        
        assert_eq!(m1, m2);
        assert_eq!(m1_merge, m2_merge);
        assert_eq!(m1, m1_merge);
        assert_eq!(m2, m2_merge);
        assert_eq!(m1, m2_merge);
        assert_eq!(m2, m1_merge);
    }
    
    #[test]
    fn test_idempotent_quickcheck1() {
        let ops = vec![
            Op::Up {
                dot: Dot { actor: 62, counter: 9 },
                key: 47,
                op: Op::Up {
                    dot: Dot { actor: 62, counter: 1 },
                    key: 65,
                    op: mvreg::Op::Put {
                        clock: Dot { actor: 62, counter: 1 }.into(),
                        val: 240
                    }
                }
            },
            Op::Up {
                dot: Dot { actor: 62, counter: 11 },
                key: 60,
                op: Op::Up {
                    dot: Dot { actor: 62, counter: 1 },
                    key: 193,
                    op: mvreg::Op::Put {
                        clock: Dot { actor: 62, counter: 1 }.into(),
                        val: 28
                    }
                }
            }
        ];
        let mut m: TestMap = Map::new();
        apply_ops(&mut m, &ops);
        let m_snapshot = m.clone();
        
        // m ^ m
        m.merge(&m_snapshot);
        
        // m ^ m = m
        assert_eq!(m, m_snapshot);
    }
    
    #[test]
    fn test_op_exchange_converges_quickcheck1() {
        let ops1 = vec![
            Op::Up {
                dot: Dot { actor: 0, counter: 3 },
                key: 9,
                op: Op::Up {
                    dot: Dot { actor: 0, counter: 3 },
                    key: 0,
                    op: mvreg::Op::Put {
                        clock: Dot { actor: 0, counter: 3 }.into(),
                        val: 0
                    }
                }
            }
        ];
        let ops2 = vec![
            Op::Up {
                dot: Dot { actor: 1, counter: 1 },
                key: 9,
                op: Op::Rm {
                    clock: Dot { actor: 1, counter: 1 }.into(),
                    key: 0
                }
            },
            Op::Rm {
                clock: Dot { actor: 1, counter: 2 }.into(),
                key: 9
            }
        ];
        
        let mut m1: TestMap = Map::new();
        let mut m2: TestMap = Map::new();
        
        apply_ops(&mut m1, &ops1);
        assert_eq!(m1.clock, Dot { actor: 0, counter: 3 }.into());
        assert_eq!(m1.entries.get(&9).unwrap().clock, Dot { actor: 0, counter: 3 }.into());
        assert_eq!(m1.entries.get(&9).unwrap().val.deferred.len(), 0);
        
        apply_ops(&mut m2, &ops2);
        assert_eq!(m2.clock, Dot { actor: 1, counter: 1 }.into());
        assert_eq!(m2.entries.get(&9), None);
        assert_eq!(m2.deferred.get(&Dot { actor: 1, counter: 2 }.into()), Some(&vec![9].into_iter().collect()));
        
        // m1 <- m2
        apply_ops(&mut m1, &ops2);
        
        // m2 <- m1
        apply_ops(&mut m2, &ops1);
        
        // m1 <- m2 == m2 <- m1
        assert_eq!(m1, m2);
        
    }
    
    fn apply_ops(map: &mut TestMap, ops: &[TestOp]) {
        for op in ops.iter().cloned() {
            map.apply(&op);
        }
    }
    
    quickcheck! {
        // TODO: add test to show equivalence of merge and Op exchange
        fn prop_op_exchange_same_as_merge(
            ops1: OpVec,
            ops2: OpVec
        ) -> TestResult {
            if ops1.0 == ops2.0 {
                return TestResult::discard();
            }
            
            let mut m1: TestMap = Map::new();
            let mut m2: TestMap = Map::new();
            
            apply_ops(&mut m1, &ops1.1);
            apply_ops(&mut m2, &ops2.1);
            
            let mut m_merged = m1.clone();
            m_merged.merge(&m2);
            
            apply_ops(&mut m1, &ops2.1);
            apply_ops(&mut m2, &ops1.1);
            
            TestResult::from_bool(m1 == m_merged && m2 == m_merged)
        }
        
        fn prop_op_exchange_converges(ops1: OpVec, ops2: OpVec) -> TestResult {
            if ops1.0 == ops2.0 {
                return TestResult::discard();
            }
            
            let mut m1: TestMap = Map::new();
            let mut m2: TestMap = Map::new();
            
            apply_ops(&mut m1, &ops1.1);
            apply_ops(&mut m2, &ops2.1);
            
            // m1 <- m2
            apply_ops(&mut m1, &ops2.1);
            
            // m2 <- m1
            apply_ops(&mut m2, &ops1.1);
            
            // m1 <- m2 == m2 <- m1
            assert_eq!(m1, m2);
            TestResult::from_bool(true)
        }
        
        fn prop_op_exchange_associative(ops1: OpVec, ops2: OpVec, ops3: OpVec) -> TestResult {
            if ops1.0 == ops2.0 || ops1.0 == ops3.0 || ops2.0 == ops3.0 {
                return TestResult::discard();
            }
            
            let mut m1: TestMap = Map::new();
            let mut m2: TestMap = Map::new();
            let mut m3: TestMap = Map::new();
            
            apply_ops(&mut m1, &ops1.1);
            apply_ops(&mut m2, &ops2.1);
            apply_ops(&mut m3, &ops3.1);
            
            // (m1 <- m2) <- m3
            apply_ops(&mut m1, &ops2.1);
            apply_ops(&mut m1, &ops3.1);
            
            // (m2 <- m3) <- m1
            apply_ops(&mut m2, &ops3.1);
            apply_ops(&mut m2, &ops1.1);
            
            // (m1 <- m2) <- m3 = (m2 <- m3) <- m1
            TestResult::from_bool(m1 == m2)
        }
        
        fn prop_op_idempotent(ops: OpVec) -> bool {
            let mut m = TestMap::new();
            
            apply_ops(&mut m, &ops.1);
            let m_snapshot = m.clone();
            apply_ops(&mut m, &ops.1);
            
            m == m_snapshot
        }
        
        fn prop_op_associative(
            ops1: OpVec,
            ops2: OpVec,
            ops3: OpVec
        ) -> TestResult {
            if ops1.0 == ops2.0 || ops1.0 == ops3.0 || ops2.0 == ops3.0 {
                return TestResult::discard();
            }
            
            let mut m1: TestMap = Map::new();
            let mut m2: TestMap = Map::new();
            let mut m3: TestMap = Map::new();
            
            apply_ops(&mut m1, &ops1.1);
            apply_ops(&mut m2, &ops2.1);
            apply_ops(&mut m3, &ops3.1);
            
            // (m1 <- m2) <- m3
            apply_ops(&mut m1, &ops2.1);
            apply_ops(&mut m1, &ops3.1);
            
            // (m2 <- m3) <- m1
            apply_ops(&mut m2, &ops3.1);
            apply_ops(&mut m2, &ops1.1);
            
            // (m1 ^ m2) ^ m3 = m1 ^ (m2 ^ m3)
            TestResult::from_bool(m1 == m2)
        }
        
        
        fn prop_merge_associative(
            ops1: OpVec,
            ops2: OpVec,
            ops3: OpVec
        ) -> TestResult {
            if ops1.0 == ops2.0 || ops1.0 == ops3.0 || ops2.0 == ops3.0 {
                return TestResult::discard();
            }
            
            let mut m1: TestMap = Map::new();
            let mut m2: TestMap = Map::new();
            let mut m3: TestMap = Map::new();
            
            apply_ops(&mut m1, &ops1.1);
            apply_ops(&mut m2, &ops2.1);
            apply_ops(&mut m3, &ops3.1);
            
            let mut m1_snapshot = m1.clone();
            
            // (m1 ^ m2) ^ m3
            m1.merge(&m2);
            m1.merge(&m3);
            
            // m1 ^ (m2 ^ m3)
            m2.merge(&m3);
            m1_snapshot.merge(&m2);
            
            // (m1 ^ m2) ^ m3 = m1 ^ (m2 ^ m3)
            TestResult::from_bool(m1 == m1_snapshot)
        }
        
        fn prop_merge_commutative(ops1: OpVec, ops2: OpVec) -> TestResult {
            if ops1.0 == ops2.0 {
                return TestResult::discard();
            }
            let mut m1: TestMap = Map::new();
            let mut m2: TestMap = Map::new();
            
            apply_ops(&mut m1, &ops1.1);
            apply_ops(&mut m2, &ops2.1);
            
            let m1_snapshot = m1.clone();
            // m1 ^ m2
            m1.merge(&m2);
            
            // m2 ^ m1
            m2.merge(&m1_snapshot);
            
            // m1 ^ m2 = m2 ^ m1
            TestResult::from_bool(m1 == m2)
        }
        
        fn prop_merge_idempotent(ops: OpVec) -> bool {
            let mut m: TestMap = Map::new();
            apply_ops(&mut m, &ops.1);
            let m_snapshot = m.clone();
            
            // m ^ m
            m.merge(&m_snapshot);
            
            // m ^ m = m
            m == m_snapshot
        }
        
        fn prop_truncate_with_empty_vclock_is_nop(ops: OpVec) -> bool {
            let mut m: TestMap = Map::new();
            apply_ops(&mut m, &ops.1);
            
            let m_snapshot = m.clone();
            m.truncate(&VClock::new());
            
            m == m_snapshot
        }
    }
}
