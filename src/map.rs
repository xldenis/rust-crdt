use serde::Serialize;
use serde::de::DeserializeOwned;

use error::Result;
use traits::{Causal, CvRDT, CmRDT};
use vclock::{VClock, Actor};
use std::collections::BTreeMap;

/// Key Trait alias to reduce redundancy in type decl.
pub trait Key: Ord + Clone + Send + Serialize + DeserializeOwned {}
impl<T: Ord + Clone + Send + Serialize + DeserializeOwned> Key for T {}

/// Val Trait alias to reduce redundancy in type decl.
pub trait Val<A: Actor>
    : Default + Clone + Send + Serialize + DeserializeOwned
      + Causal<A> + CmRDT + CvRDT {}
impl<A, T> Val<A> for T where
    A: Actor,
    T: Default + Clone + Send + Serialize + DeserializeOwned
       + Causal<A> + CmRDT + CvRDT
{}

/// The Map CRDT - Supports Composition of CRDT's.
///
/// Orswot based Map with reset-remove semantics.
///
/// Reset-remove here means that if one replica removes an entry while
/// concurrently another actor mutates that entry, on merge, we will see that
/// the key is still in the map but all changes seen by the removing replica
/// will disapear from the entry. To understand this more clearly see the
/// following example:
///
/// ``` rust
/// use crdts::{Map, Orswot};
/// use crdts::CvRDT;
///
/// type Actor = u64;
/// type Friend = String;
/// let mut friend_map: Map<Friend, Orswot<Friend, Actor>, Actor> = Map::new();
///
/// let first_actor_id = 10837103590;
///
/// friend_map.update(
///     "alice".to_string(),
///     |mut friend_set| {
///         let op = friend_set.add("bob".to_string(), first_actor_id);
///         Some(op)
///     },
///     first_actor_id
/// );
///
/// let mut second_friend_map = friend_map.clone();
/// let second_actor_id = 8947212;
///
/// // now the two maps will start to diverge. first map will remove "alice"
/// // from the map while the second map will update the "alice" friend set to
/// // include "clyde".
///
/// friend_map.rm("alice".to_string(), first_actor_id);
/// second_friend_map.update(
///     "alice".to_string(),
///     |mut friend_set| {
///         Some(friend_set.add("clyde".to_string(), second_actor_id))
///     },
///     second_actor_id
/// );
///
/// // On merge, we should see that the "alice" key is in the map but the
/// // "alice" friend set only contains clyde. This is the reset-remove
/// // semantics, all changes that the removing replica saw are
/// // gone, but changes not seen by the removing replica are kept.
///
/// friend_map.merge(&second_friend_map).unwrap();
///
/// let alice_friends = friend_map.get(&"alice".to_string());
///
/// match alice_friends {
///     Some(set) => assert_eq!(set.value(), vec!["clyde".to_string()]),
///     None => panic!()
/// }
/// ```
#[serde(bound(deserialize = ""))]
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Map<K: Key, V: Val<A>, A: Actor> {
    // This clock stores the current version of the Map, it should
    // be greator or equal to all Entry.clock's in the Map.
    clock: VClock<A>,
    entries: BTreeMap<K, Entry<V, A>>
}

#[serde(bound(deserialize = ""))]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
struct Entry<V: Val<A>, A: Actor> {
    // The entry clock tells us which actors have last changed this entry.
    // This clock will tell us what to do with this entry in the case of a merge
    // where only one map has this entry.
    //
    // e.g. say replica A has key `"user_32"` but replica B does not. We need to
    // decide whether replica B has processed an `rm("user_32")` operation
    // and replica A has not or replica A has processed a update("key")
    // operation which has not been seen by replica B yet.
    //
    // This conflict can be resolved by comparing replica B's Map.clock to the
    // the "user_32" Entry clock in replica A.
    // If B's clock is >=  "user_32"'s clock, then we know that B has
    // seen this entry and removed it, otherwise B has not received the update
    // operation so we keep the key.
    clock: VClock<A>,

    // The nested CRDT
    val: V
}

/// Operations which can be applied to the Map CRDT
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Op<K: Key, V: Val<A>, A: Actor> {
    /// No change to the CRDT
    Nop,
    /// Remove a key from the map
    Rm {
        /// Remove context
        clock: VClock<A>,
        /// Key to remove
        key: K
    },
    /// Update an entry in the map
    Up {
        /// Update context
        clock: VClock<A>,
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

        self.clock.subtract(&clock);
    }
}

impl<K: Key, V: Val<A>, A: Actor> CmRDT for Map<K, V, A> {
    type Op = Op<K, V, A>;

    fn apply(&mut self, op: &Self::Op) -> Result<()> {
        match op.clone() {
            Op::Nop => {/* do nothing */},
            Op::Rm { clock, key } => {
                // TODO: grep for truncates with cloned clock, we changed the api
                //       to take a reference
                if !(self.clock >= clock) {
                    if let Some(mut entry) = self.entries.remove(&key) {
                        entry.clock.subtract(&clock);
                        if !entry.clock.is_empty() {
                            entry.val.truncate(&clock);
                            self.entries.insert(key, entry);
                        } else {
                            // the entries clock has been dominated by the
                            // remove op clock, so we remove (already did)
                        }
                    }
                    self.clock.merge(&clock);
                }
            },
            Op::Up { clock, key, op } => {
                if !(self.clock >= clock) {
                    let mut entry = self.entries.remove(&key)
                        .unwrap_or_else(|| Entry {
                            clock: clock.clone(),
                            val: V::default()
                        });

                    entry.clock.merge(&clock);
                    entry.val.apply(&op)?;
                    self.entries.insert(key.clone(), entry);
                    self.clock.merge(&clock);
                }
            }
        }
        Ok(())
    }
}

impl<K: Key, V: Val<A>, A: Actor> CvRDT for Map<K, V, A> {    
    fn merge(&mut self, other: &Self) -> Result<()> {
        for (key, entry) in other.entries.iter() {
            // TODO(david) avoid this remove here with entries.get_mut?
            if let Some(mut existing) = self.entries.remove(&key) {
                existing.clock.merge(&entry.clock);
                existing.val.merge(&entry.val).unwrap(); // TODO: unwrap
                self.entries.insert(key.clone(), existing);
            } else {
                // we don't have this entry:
                //   is this because we removed it?
                if self.clock > entry.clock {
                    // we removed this entry! don't add it back to our map
                    continue;
                }

                // this is either a new entry, or an entry we removed while the
                // other map has concurrently mutated it. (reset-remove)
                let mut new_entry = entry.clone();

                let truncate_clock: VClock<A> = self.clock.clone()
                    .into_iter()
                    .filter(|(a, c)| c > &new_entry.clock.get(&a))
                    .collect();
                new_entry.val.truncate(&truncate_clock);
                self.entries.insert(key.clone(), new_entry);
            }
        }

        // check for entries that we have but are missing in other
        let mut to_remove = Vec::new();
        for (key, mut entry) in self.entries.iter_mut() {
            if other.entries.get(&key).is_some() {
                // The entry exists, we've already dealt with it above
                continue;
            }
            if other.clock >= entry.clock {
                // other has seen this entry and removed it, we remove it
                to_remove.push(key.clone());
            } else if other.clock.concurrent(&entry.clock) {
                // other has removed this entry but we modified it concurrently
                // (reset-remove)
                let truncate_clock: VClock<A> = other.clock.clone()
                    .into_iter()
                    .filter(|(a, c)| c > &entry.clock.get(&a))
                    .collect();
                entry.val.truncate(&truncate_clock);
            } else {
                // our entry clock is ahead of the other's clock meaning we have
                // seen everything the other has seen. We have nothing to do.
            }
        }

        for key in to_remove.into_iter() {
            self.entries.remove(&key);
        }

        self.clock.merge(&other.clock);
        Ok(())
    }
}

impl<K: Key, V: Val<A>, A: Actor> Map<K, V, A> {
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

    /// Get a reference to a value stored under a key
    pub fn get(&self, key: &K) -> Option<&V> {
        self.entries.get(&key)
            .map(|map_entry| &map_entry.val)
    }

    /// Update a value under some key, if the key is not present in the map,
    /// the updater will be given `None`, otherwise `Some(val)` is given.
    ///
    /// The updater must return Some(val) to have the updated val stored back in
    /// the Map. If None is returned, this entry is removed from the Map.
    pub fn update<F>(&mut self, key: K, updater: F, actor: A) -> Op<K, V, A> where
        F: FnOnce(V) -> Option<V::Op>
    {
        let mut clock = self.clock.clone();
        clock.increment(actor.clone());

        let val_opt = self.entries.get(&key)
            .map(|entry| entry.val.clone());
        let val_exists = val_opt.is_some();
        let val = val_opt.unwrap_or(V::default());

        let op = if let Some(op) = updater(val) {
            Op::Up { clock, key, op }
        } else if val_exists {
            Op::Rm { clock, key }
        } else {
            Op::Nop
        };

        self.apply(&op).unwrap(); // this must not fail
        op
    }

    /// Remove an entry from the Map
    pub fn rm(&mut self, key: K, actor: A) -> Op<K, V, A> {
        let mut clock = self.clock.clone();
        clock.increment(actor.clone());
        let op = Op::Rm { clock, key };
        self.apply(&op).unwrap(); // this must not fail
        op
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use lwwreg::LWWReg;

    use quickcheck::{Arbitrary, Gen, TestResult};
    type TestActor = u8;
    type TestKey = u8;
    type TestVal = LWWReg<u8, (u64, TestActor)>;
    type TestOp = Op<TestKey, Map<TestKey, TestVal, TestActor>, TestActor>;
    type TestMap =  Map<TestKey, Map<TestKey, TestVal, TestActor>, TestActor>;

    // We can't impl on types outside this module ie. '(u8, Vec<_>)' so we wrap.
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
                            })
                            .collect::<Vec<Self>>()
                    );

                    shrunk.push(Op::Nop);
                },
                Op::Up { clock, key, op } => {
                    shrunk.extend(
                        clock.shrink()
                            .map(|c| Op::Up {
                                clock: c,
                                key: key.clone(),
                                op: op.clone()
                            })
                            .collect::<Vec<Self>>()
                    );
                    shrunk.extend(
                        key.shrink()
                            .map(|k| Op::Up {
                                clock: clock.clone(),
                                key: k,
                                op: op.clone() })
                            .collect::<Vec<Self>>()
                    );
                    shrunk.extend(
                        op.shrink()
                            .map(|o| Op::Up {
                                clock: clock.clone(),
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
            let mut map = Map::new();
            let num_entries: u8 = g.gen_range(0, 10);
            for _ in 0..num_entries {
                let reg = TestVal::arbitrary(g);
                let actor = reg.dot.1.clone();
                map.update(g.gen(), |_| Some(reg), actor);
            }
            map
        }

        fn shrink(&self) -> Box<Iterator<Item = Map<TestKey, TestVal, TestActor>>> {
            let mut shrunk = Vec::new();
            for dot in self.clock.clone().into_iter() {
                let mut map = self.clone();
                let clock: VClock<u8> = self.clock
                    .clone()
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

            for (key, entry) in self.entries.iter() {
                for val in entry.val.shrink() {
                    let mut map = self.clone();
                    let mut shrunk_entry = entry.clone();
                    shrunk_entry.val = val;
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
            let num_ops: u8 = g.gen_range(0, 10); // max 255 ops should be ok for tests
            
            let mut map = TestMap::new();
            let mut ops = Vec::with_capacity(num_ops as usize);
            for _ in 0..num_ops {
                let die_roll: u8 = g.gen();
                let key = g.gen();
                let op = match die_roll % 3 {
                    0 => {
                        // update inner map
                        map.update(key, |mut inner_map| {
                            let die_roll: u8 = g.gen();
                            let key = g.gen();
                            match die_roll % 4 {
                                0 => {
                                    // update key rm
                                    let op = inner_map.update(key, |_| None, actor.clone());
                                    Some(op)
                                },
                                1 => {
                                    // update key and val update
                                    let op = inner_map.update(key, |mut reg| {
                                        reg.update(g.gen(), (g.gen(), actor.clone())).unwrap();
                                        Some(reg)
                                    }, actor.clone());
                                    Some(op)
                                },
                                2 => {
                                    // inner rm
                                    let op = inner_map.rm(key, actor.clone());
                                    Some(op)
                                },
                                _ => {
                                    // rm
                                    None
                                }
                            }
                        }, actor.clone())
                    },
                    1 => {
                        // rm
                        let key = g.gen();
                        map.rm(key, actor.clone())
                    },
                    _ => {
                        // nop
                        Op::Nop
                    }
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

            for i in 0..self.1.len() {
                for shrunk_op in self.1[i].shrink() {
                    let mut vec = self.1.clone();
                    vec[i] = shrunk_op;
                    shrunk.push(OpVec(self.0, vec));
                }
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

        assert_eq!(m.get(&0), Some(&Map::new()));
    }

    #[test]
    fn test_update() {
        let mut m: TestMap = Map::new();

        // constructs a default value if does not exist
        m.update(
            101,
            |mut map| {
                Some(map.update(110, |mut reg| {
                    let new_val = (reg.val + 1) * 2;
                    let new_dot = (reg.dot.0 + 1, 1);
                    assert!(reg.update(new_val, new_dot).is_ok());
                    Some(reg)
                }, 1))
            },
            1
        );
        assert_eq!(m.get(&101).unwrap().get(&110), Some(&LWWReg { val: 2, dot: (1, 1) }));

        // Updating once more, the map should give the latest val to the function
        m.update(
            101,
            |mut map| {
                Some(map.update(110, |mut reg| {
                    assert_eq!(reg, LWWReg { val: 2, dot: (1, 1) });
                    let new_val = (reg.val + 1) * 2;
                    let new_dot = (reg.dot.0 + 1, 1);
                    assert!(reg.update(new_val, new_dot).is_ok());
                    Some(reg)
                }, 1))
            },
            1
        );

        assert_eq!(m.get(&101).unwrap().get(&110), Some(&LWWReg { val: 6, dot: (2, 1) }));

        // Returning None from the closure should remove the element
        m.update(101, |_| None, 1);

        assert_eq!(m.get(&101), None);
    }

    #[test]
    fn test_remove() {
        let mut m: TestMap = Map::new();

        m.update(101, |mut m| Some(m.update(110, |r| Some(r), 1)), 1);
        let mut inner_map = Map::new();
        inner_map.update(110, |r| Some(r), 1);
        assert_eq!(m.get(&101), Some(&inner_map));
        assert_eq!(m.len(), 1);

        m.rm(101, 1);
        assert_eq!(m.get(&101), None);
        assert_eq!(m.len(), 0);
    }

    #[test]
    fn test_reset_remove_semantics() {
        let mut m1 = TestMap::new();
        m1.update(
            101,
            |mut map| {
                let op = map.update(
                    110,
                    |mut reg| {
                        reg.update(32, (0, 74)).unwrap();
                        Some(reg)
                    },
                    74
                );
                Some(op)
            },
            74
        );

        let mut m2 = m1.clone();

        m1.rm(101, 74);

        m2.update(
            101,
            |mut map| {
                let op = map.update(
                    220,
                    |mut reg| {
                        reg.update(5, (0, 37)).unwrap();
                        Some(reg)
                    },
                    37
                );
                Some(op)
            },
            37
        );

        let m1_snapshot = m1.clone();
        assert!(m1.merge(&m2).is_ok());
        assert!(m2.merge(&m1_snapshot).is_ok());

        assert_eq!(m1, m2);

        let inner_map = m1.get(&101).unwrap();
        assert_eq!(inner_map.get(&220), Some(&LWWReg { val: 5, dot: (0, 37) }));
        assert_eq!(inner_map.get(&110), None);
        assert_eq!(inner_map.len(), 1);
    }

    #[test]
    fn test_updating_with_current_clock_should_be_a_nop() {
        let mut m1: TestMap = Map::new();

        let res = m1.apply(&Op::Up {
            clock: VClock::new(),
            key: 0,
            op: Op::Up {
                clock: VClock::new(),
                key: 1,
                op: LWWReg {
                    val: 0,
                    dot: (0, 0)
                }
            }
        });

        assert!(res.is_ok());

        // the update should have been ignored
        assert_eq!(m1, Map::new());
    }

    #[test]
    fn test_concurrent_update_and_remove() {
        let mut m1 = TestMap::new();
        let mut m2 = TestMap::new();

        let op1 = m1.rm(102, 75);
        // TAI: try with an update instead of a Nop
        let op2 = m2.update(102, |_| Some(Op::Nop), 61);
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
    fn test_order_of_remove_and_update_does_not_matter() {
        let mut m1 = TestMap::new();
        let mut m2 = TestMap::new();

        let op1 = m1.update(0, |_| Some(Op::Nop), 35);
        let op2 = m2.rm(1, 47);

        let mut m1_clone = m1.clone();
        let mut m2_clone = m2.clone();

        assert!(m1_clone.merge(&m2).is_ok());
        assert!(m2_clone.merge(&m1).is_ok());

        assert_eq!(m1_clone, m2_clone);

        assert!(m1.apply(&op2).is_ok());
        assert!(m2.apply(&op1).is_ok());

        assert_eq!(m1, m2);

        assert_eq!(m1, m1_clone);
    }

    #[test]
    fn test_commute_dunno() {
        let ops = vec![
            Op::Rm {
                clock: vec![(45, 1)].into_iter().collect(),
                key: 0
            },
            Op::Up {
                clock: vec![(45, 2)].into_iter().collect(),
                key: 0,
                op: Op::Up {
                    clock: vec![(45, 1)].into_iter().collect(),
                    key: 0,
                    op: LWWReg { val: 0, dot: (0, 0) }
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
    fn test_idempotent_dunno() {
        let ops = vec![
            Op::Up {
                clock: vec![(21, 5)].into_iter().collect(),
                key: 0,
                op: Op::Nop
            },
            Op::Up {
                clock: vec![(21, 6)].into_iter().collect(),
                key: 1,
                op: Op::Up {
                    clock: vec![(21, 1)].into_iter().collect(),
                    key: 0,
                    op: LWWReg { val: 0, dot: (0, 0) }
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
    fn test_dunno() {
        let mut m: TestMap = Map::new();
        let res = m.apply(&Op::Up {
            clock: vec![(32, 5)].into_iter().collect(),
            key: 0,
            op: Op::Up {
                clock: vec![(32, 1)].into_iter().collect(),
                key: 0,
                op: LWWReg {
                    val: 0,
                    dot: (0, 0)
                }
            }
        });

        assert!(res.is_ok());

        let m_snapshot = m.clone();

        // m ^ m
        assert!(m.merge(&m_snapshot).is_ok());

        // m ^ m = m
        assert_eq!(m, m_snapshot);
    }

    fn apply_ops(map: &mut TestMap, ops: &[TestOp]) {
        for op in ops.iter() {
            map.apply(op).unwrap()
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

        fn prop_exchange_ops_converges(ops1: OpVec, ops2: OpVec) -> TestResult {
            if ops1.0 == ops2.0 {
                return TestResult::discard();
            }

            let mut m1: TestMap = Map::new();
            let mut m2: TestMap = Map::new();

            apply_ops(&mut m1, &ops1.1);
            apply_ops(&mut m2, &ops2.1);

            apply_ops(&mut m1, &ops2.1);
            apply_ops(&mut m2, &ops1.1);

            TestResult::from_bool(m1 == m2)
        }

        fn prop_truncate_with_empty_vclock_is_nop(ops: OpVec) -> bool {
            let mut m: TestMap = Map::new();
            apply_ops(&mut m, &ops.1);

            let m_snapshot = m.clone();
            m.truncate(&VClock::new());

            m == m_snapshot
        }

        fn prop_associative(
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

        fn prop_commutative(ops1: OpVec, ops2: OpVec) -> TestResult {
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

        fn prop_idempotent(ops: OpVec) -> bool {
            let mut m: TestMap = Map::new();
            apply_ops(&mut m, &ops.1);
            let m_snapshot = m.clone();

            // m ^ m
            assert!(m.merge(&m_snapshot).is_ok());

            // m ^ m = m
            m == m_snapshot
        }
    }
}
