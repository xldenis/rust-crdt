use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Debug;

use serde::Serialize;
use serde::de::DeserializeOwned;

use error::{self, Error, Result};
use traits::{Causal, CvRDT, CmRDT};
use vclock::{Dot, VClock, Actor};

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
/// let a1 = 10837103590; // initial actors id
///
/// let op = friends.update(
///     "alice".into(),
///     friends.dot(a1),
///     |set, dot| set.add("bob".into(), dot)
/// );
/// friends.apply(&op);
///
/// let mut friends_replica = friends.clone();
/// let a2 = 8947212; // the replica's actor id
///
/// // now the two maps diverge. the original map will remove "alice" from the map
/// // while the replica map will update the "alice" friend set to include "clyde".
///
/// let (_, rm_ctx) = friends.get(&"alice".to_string()).unwrap();
/// let rm_op = friends.rm("alice".into(), rm_ctx);
/// friends.apply(&rm_op);
///
/// let replica_op = friends_replica.update(
///     "alice".into(),
///     friends_replica.dot(a2),
///     |set, dot| set.add("clyde".into(), dot)
/// );
/// friends_replica.apply(&replica_op);
///
/// assert_eq!(friends.get(&"alice".into()), None);
/// assert_eq!(
///     friends_replica.get(&"alice".into()).map(|(s, _)| s.value()),
///     Some(vec!["bob".to_string(), "clyde".to_string()])
/// );
///
/// // On merge, we should see "alice" in the map but her friend set should only have "clyde".
///
/// assert!(friends.merge(&friends_replica).is_ok());
///
/// let alice_friends = friends.get(&"alice".into())
///     .map(|(s, _)| s.value());
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
        /// The entry's clock at the time of the remove
        context: VClock<A>,
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
    type Error = error::Error;
    type Op = Op<K, V, A>;

    fn apply(&mut self, op: &Self::Op) -> Result<()> {
        match op.clone() {
            Op::Nop => {/* do nothing */},
            Op::Rm { context, key } => {
                self.apply_rm(key, &context);
            },
            Op::Up { dot: Dot { actor, counter }, key, op } => {
                if self.clock.get(&actor) >= counter {
                    // we've seen this op already
                    return Ok(())
                }

                let mut entry = self.entries.remove(&key)
                    .unwrap_or_else(|| Entry {
                        clock: VClock::new(),
                        val: V::default()
                    });

                entry.clock.witness(actor.clone(), counter).unwrap();
                entry.val.apply(&op).map_err(|_| Error::NestedOpFailed)?;
                self.entries.insert(key.clone(), entry);

                self.clock.witness(actor, counter).unwrap();
                self.apply_deferred();
            }
        }
        Ok(())
    }
}

impl<K: Key, V: Val<A>, A: Actor> CvRDT for Map<K, V, A> {
    type Error = error::Error;

    fn merge(&mut self, other: &Self) -> Result<()> {
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
                        entry.val.merge(&other_entry.val).unwrap();
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
        Ok(())
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

    pub fn dot(&self, actor: A) -> Dot<A> {
        let counter = self.clock.get(&actor) + 1;
        Dot { actor, counter }
    }

    /// Returns the number of entries in the Map
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Get a reference to a value stored under a key
    pub fn get(&self, key: &K) -> Option<(&V, VClock<A>)> {
        self.entries.get(&key)
            .map(|map_entry| (&map_entry.val, map_entry.clock.clone()))
    }

    /// Update a value under some key, if the key is not present in the map,
    /// the updater will be given the result of V::default().
    pub fn update<U>(&self, key: K, dot: Dot<A>, updater: U) -> Op<K, V, A>
        where U: FnOnce(&V, Dot<A>) -> V::Op
    {
        let op = if let Some(entry) = self.entries.get(&key) {
            updater(&entry.val, dot.clone())
        } else {
            updater(&V::default(), dot.clone())
        };
        Op::Up { dot, key, op }
    }

    /// Remove an entry from the Map
    pub fn rm(&self, key: K, context: VClock<A>) -> Op<K, V, A> {
        Op::Rm { context, key }
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

    /// Apply a key removal given a context.
    fn apply_rm(&mut self, key: K, context: &VClock<A>) {
        if !context.dominating_vclock(&self.clock).is_empty() {
            let deferred_set = self.deferred.entry(context.clone())
                .or_insert_with(|| BTreeSet::new());
            deferred_set.insert(key.clone());
        }

        if let Some(mut existing_entry) = self.entries.remove(&key) {
            let dom_clock = existing_entry.clock.dominating_vclock(&context);
            if !dom_clock.is_empty() {
                existing_entry.clock = dom_clock;
                existing_entry.val.truncate(&context);
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
                Op::Rm { context, key } => {
                    shrunk.extend(
                        context.shrink()
                            .map(|c| Op::Rm {
                                context: c,
                                key: key.clone()
                            })
                            .collect::<Vec<Self>>()
                    );

                    shrunk.extend(
                        key.shrink()
                            .map(|k| Op::Rm {
                                context: context.clone(),
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
                let key = g.gen();
                let actor = g.gen_range(0, 10);
                let coin_toss = g.gen();
                let op = match coin_toss {
                    true =>
                        map.update(key, map.dot(actor), |r, dot| r.set(g.gen(), dot)),
                    false =>
                        map.rm(key, VClock::arbitrary(g))
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
                let context: VClock<_> = Dot { actor, counter: i as u64 }.into();
                // context = context.into_iter().filter(|(a, _)| a != &actor).collect();
                // context.witness(actor.clone(), i as u64).unwrap();
                let op = match die_roll % 3 {
                    0 => {
                        let dot = Dot { actor, counter: context.get(&actor) };
                        Op::Up {
                            dot: dot.clone(),
                            key: g.gen(),
                            op: match die_roll_inner % 3 {
                                0 => Op::Up {
                                    dot: dot.clone(),
                                    key: g.gen(),
                                    op: mvreg::Op::Put {
                                        context,
                                        val: g.gen()
                                    }
                                },
                                1 => Op::Rm {
                                    context,
                                    key: g.gen()
                                },
                                _ => Op::Nop
                            }
                        }
                    },
                    1 => Op::Rm { context, key: g.gen() },
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
        assert_eq!(m.len(), 0);
    }

    #[test]
    fn test_get() {
        let mut m: TestMap = Map::new();

        assert_eq!(m.get(&0), None);

        m.clock.increment(1);
        m.entries.insert(0, Entry {
            clock: m.clock.clone(),
            val: Map::default()
        });

        assert_eq!(m.get(&0), Some((&Map::new(), m.clock.clone())));
    }

    #[test]
    fn test_update() {
        let mut m: TestMap = Map::new();

        // constructs a default value if does not exist
        let op = m.update(101, m.dot(1), |map, dot| {
            map.update(110, dot, |reg, dot| reg.set(2, dot))
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
                        context: Dot { actor: 1, counter: 1 }.into(),
                        val: 2
                    }
                }
            }
        );

        assert_eq!(m, Map::new());

        m.apply(&op);

        assert_eq!(
            m.get(&101)
                .and_then(|(m2, _)| m2.get(&110))
                .map(|(r, _)| r.get().0),
            Some(vec![&2])
        );

        // the map should give the latest val to the closure
        let op2 = m.update(101, m.dot(1), |map, dot| {
            map.update(110, dot, |reg, dot| {
                assert_eq!(reg.get().0, vec![&2]);
                reg.set(6, dot)
            })
        });
        m.apply(&op2);

        assert_eq!(
            m.get(&101)
                .and_then(|(m2, _)| m2.get(&110))
                .map(|(r, _)| r.get().0),
            Some(vec![&6])
        );
    }

    #[test]
    fn test_remove() {
        let mut m: TestMap = Map::new();

        let op = m.update(101, m.dot(1), |m, dot| m.update(110, dot, |r, dot| r.set(0, dot)));
        let mut inner_map: Map<TestKey, TestVal, TestActor> = Map::new();
        let inner_op = inner_map.update(110, m.dot(1), |r, dot| r.set(0, dot));
        inner_map.apply(&inner_op);

        m.apply(&op);

        let rm_op = {
            let (val, ctx) = m.get(&101).unwrap();
            assert_eq!(val, &inner_map);
            assert_eq!(m.len(), 1);
            m.rm(101, ctx)
        };
        m.apply(&rm_op);
        assert_eq!(m.get(&101), None);
        assert_eq!(m.len(), 0);
    }

    #[test]
    fn test_reset_remove_semantics() {
        let mut m1 = TestMap::new();
        let op1 = m1.update(101, m1.dot(74), |map, dot| {
            map.update(110, dot, |reg, dot| {
                reg.set(32, dot)
            })
        });
        m1.apply(&op1);

        let mut m2 = m1.clone();

        let (_, ctx) = m1.get(&101).unwrap();

        let op2 = m1.rm(101, ctx);
        m1.apply(&op2);

        let op3 = m2.update(101, m2.dot(37), |map, dot| {
            map.update(220, dot, |reg, dot| {
                reg.set(5, dot)
            })
        });
        m2.apply(&op3);

        let m1_snapshot = m1.clone();
        
        assert!(m1.merge(&m2).is_ok());
        assert!(m2.merge(&m1_snapshot).is_ok());
        assert_eq!(m1, m2);

        let (inner_map, _) = m1.get(&101).unwrap();
        assert_eq!(inner_map.get(&220).unwrap().0.get().0, vec![&5]);
        assert_eq!(inner_map.get(&110), None);
        assert_eq!(inner_map.len(), 1);
    }
    
    #[test]
    fn test_updating_with_current_clock_should_be_a_nop() {
        let mut m1: TestMap = Map::new();

        let res = m1.apply(&Op::Up {
            dot: Dot { actor: 1, counter: 0 },
            key: 0,
            op: Op::Up {
                dot: Dot { actor: 1, counter: 0 },
                key: 1,
                op: mvreg::Op::Put {
                    context: VClock::new(),
                    val: 235
                }
            }
        });

        assert!(res.is_ok());

        // the update should have been ignored
        assert_eq!(m1, Map::new());
    }

    #[test]
    fn test_concurrent_update_and_remove_add_bias() {
        let mut m1 = TestMap::new();
        let mut m2 = TestMap::new();

        let op1 = Op::Rm {
            context: Dot { actor: 1, counter: 1 }.into(),
            key: 102
        };
        let op2 = m2.update(102, m2.dot(2), |_, _| Op::Nop);

        m1.apply(&op1.clone());
        m2.apply(&op2.clone());

        let mut m1_clone = m1.clone();
        let mut m2_clone = m2.clone();

        assert!(m1_clone.merge(&m2).is_ok());
        assert!(m2_clone.merge(&m1).is_ok());

        assert_eq!(m1_clone, m2_clone);

        assert!(m1.apply(&op2).is_ok());
        assert!(m2.apply(&op1).is_ok());

        assert_eq!(m1, m2);

        assert_eq!(m1, m1_clone);

        // we bias towards adds
        assert!(m1.get(&102).is_some());
    }

    #[test]
    fn test_op_exchange_commutes_quickcheck1() {
        // THIS WILL NOT PASS IF WE SWAP OUT THE MVREG WITH AN LWWREG
        // we need a true causal register
        let mut m1: Map<u8, MVReg<u8, u8>, u8> = Map::new();
        let mut m2: Map<u8, MVReg<u8, u8>, u8> = Map::new();

        let m1_op1 = m1.update(0, m1.dot(1), |reg, dot| reg.set(0, dot));
        m1.apply(&m1_op1);

        let m1_op2 = m1.rm(0, m1.get(&0).unwrap().1);
        m1.apply(&m1_op2);

        let m2_op1 = m2.update(0, m2.dot(2), |reg, dot| reg.set(0, dot));
        m2.apply(&m2_op1);

        // m1 <- m2
        assert!(m1.apply(&m2_op1).is_ok());

        // m2 <- m1
        assert!(m2.apply(&m1_op1).is_ok());
        assert!(m2.apply(&m1_op2).is_ok());

        assert_eq!(m1, m2);
    }

    #[test]
    fn test_op_deferred_remove() {
        let mut m1 = TestMap::new();
        let mut m2 = TestMap::new();
        let mut m3 = TestMap::new();

        let m1_up1 = m1.update(0, m1.dot(1), |map, dot| map.update(0, dot, |reg, dot| {
            reg.set(0, dot)
        }));
        m1.apply(&m1_up1).unwrap();

        let m1_up2 = m1.update(1, m1.dot(1), |map, dot| map.update(1, dot, |reg, dot| {
            reg.set(1, dot)
        }));
        m1.apply(&m1_up2).unwrap();

        assert!(m2.apply(&m1_up1).is_ok());
        assert!(m2.apply(&m1_up2).is_ok());

        let (_, ctx) = m2.get(&0).unwrap();
        let m2_rm = m2.rm(0, ctx);
        m2.apply(&m2_rm).unwrap();
        
        assert_eq!(m2.get(&0), None);
        assert!(m3.apply(&m2_rm).is_ok());
        assert_eq!(m3.deferred.len(), 1);
        assert!(m3.apply(&m1_up1).is_ok());
        assert_eq!(m3.deferred.len(), 0);
        assert!(m3.apply(&m1_up2).is_ok());

        assert!(m1.apply(&m2_rm).is_ok());

        assert_eq!(m2.get(&0), None);
        assert_eq!(
            m3.get(&1)
                .and_then(|(inner, _)| inner.get(&1))
                .map(|(r, _)| r.get().0),
            Some(vec![&1])
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

        let m1_up1 = m1.update(0, m1.dot(1), |map, dot| map.update(0, dot, |reg, dot| {
            reg.set(0, dot)
        }));
        m1.apply(&m1_up1);

        let m1_up2 = m1.update(1, m1.dot(1), |map, dot| map.update(1, dot, |reg, dot| {
            reg.set(1, dot)
        }));
        m1.apply(&m1_up2);

        assert!(m2.apply(&m1_up1).is_ok());
        assert!(m2.apply(&m1_up2).is_ok());

        let (_, ctx) = m2.get(&0).unwrap();
        let m2_rm = m2.rm(0, ctx);
        m2.apply(&m2_rm);

        assert!(m3.merge(&m2).is_ok());
        assert!(m3.merge(&m1).is_ok());
        assert!(m1.merge(&m2).is_ok());

        assert_eq!(m2.get(&0), None);
        assert_eq!(
            m3.get(&1)
                .and_then(|(inner, _)| inner.get(&1))
                .map(|(r, _)| r.get().0),
            Some(vec![&1])
        );
        
        assert_eq!(m2, m3);
        assert_eq!(m1, m2);
        assert_eq!(m1, m3);
    }

    #[test]
    fn test_commute_quickcheck_bug() {
        let ops = vec![
            Op::Rm {
                context: Dot { actor: 45, counter: 1 }.into(),
                key: 0
            },
            Op::Up {
                dot: Dot { actor: 45, counter: 2 },
                key: 0,
                op: Op::Up {
                    dot: Dot { actor: 45, counter: 1 },
                    key: 0,
                    op: mvreg::Op::Put { context: VClock::new(), val: 0 }
                }
            }
        ];

        let mut m = Map::new();
        apply_ops(&mut m, &ops);

        let m_snapshot = m.clone();

        let mut empty_m = Map::new();
        assert!(m.merge(&empty_m).is_ok());
        assert!(empty_m.merge(&m_snapshot).is_ok());

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
                    op: mvreg::Op::Put { context: VClock::new(), val: 0 }
                }
            }
        ];

        let mut m = Map::new();
        apply_ops(&mut m, &ops);

        let m_snapshot = m.clone();
        assert!(m.merge(&m_snapshot).is_ok());

        assert_eq!(m, m_snapshot);
    }

    #[test]
    fn test_idempotent_quickcheck_bug2() {
        let mut m: TestMap = Map::new();
        let res = m.apply(&Op::Up {
            dot: Dot { actor: 32, counter: 5 },
            key: 0,
            op: Op::Up {
                dot: Dot { actor: 32, counter: 5 },
                key: 0,
                op: mvreg::Op::Put { context: VClock::new(), val: 0 }
            }
        });

        assert!(res.is_ok());

        let m_snapshot = m.clone();

        // m ^ m
        assert!(m.merge(&m_snapshot).is_ok());

        // m ^ m = m
        assert_eq!(m, m_snapshot);
    }

    #[test]
    fn test_nop_on_new_map_should_remain_a_new_map() {
        let mut map = TestMap::new();
        map.apply(&Op::Nop).unwrap();
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
                    context: Dot { actor: 91, counter: 1 }.into(),
                    val: 94
                }
            }
        };
        let mut m1: TestMap = Map::new();
        let mut m2: TestMap = Map::new();
        m1.apply(&op1).unwrap();
        m2.apply(&op2).unwrap();

        let mut m1_merge = m1.clone();
        assert!(m1_merge.merge(&m2).is_ok());
        
        let mut m2_merge = m2.clone();
        assert!(m2_merge.merge(&m1).is_ok());

        m1.apply(&op2).unwrap();
        m2.apply(&op1).unwrap();


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
                        context: Dot { actor: 62, counter: 1 }.into(),
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
                        context: Dot { actor: 62, counter: 1 }.into(),
                        val: 28
                    }
                }
            }
        ];
        let mut m: TestMap = Map::new();
        apply_ops(&mut m, &ops);
        let m_snapshot = m.clone();

        // m ^ m
        assert!(m.merge(&m_snapshot).is_ok());

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
                        context: Dot { actor: 0, counter: 3 }.into(),
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
                    context: Dot { actor: 1, counter: 1 }.into(),
                    key: 0
                }
            },
            Op::Rm {
                context: Dot { actor: 1, counter: 2 }.into(),
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
            map.apply(&op).unwrap()
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
            assert!(m_merged.merge(&m2).is_ok());

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
            assert!(m1.merge(&m2).is_ok());
            assert!(m1.merge(&m3).is_ok());

            // m1 ^ (m2 ^ m3)
            assert!(m2.merge(&m3).is_ok());
            assert!(m1_snapshot.merge(&m2).is_ok());

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
            assert!(m1.merge(&m2).is_ok());

            // m2 ^ m1
            assert!(m2.merge(&m1_snapshot).is_ok());

            // m1 ^ m2 = m2 ^ m1
            TestResult::from_bool(m1 == m2)
        }

        fn prop_merge_idempotent(ops: OpVec) -> bool {
            let mut m: TestMap = Map::new();
            apply_ops(&mut m, &ops.1);
            let m_snapshot = m.clone();

            // m ^ m
            assert!(m.merge(&m_snapshot).is_ok());

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
