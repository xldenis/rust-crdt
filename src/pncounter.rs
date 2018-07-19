use std::cmp::Ordering;

use vclock::Actor;
use gcounter::GCounter;

/// `PNCounter` allows the counter to be both incremented and decremented
/// by representing the increments (P) and the decrements (N) in separate
/// internal G-Counters.
///
/// Merge is implemented by merging the internal P and N counters.
/// The value of the counter is P minus N.
///
/// # Examples
///
/// ```
/// use crdts::PNCounter;
/// let mut a = PNCounter::new();
/// a.increment("A".to_string());
/// a.increment("A".to_string());
/// a.decrement("A".to_string());
/// a.increment("A".to_string());
/// assert_eq!(a.value(), 2);
/// ```
#[serde(bound(deserialize = ""))]
#[derive(Debug, Eq, Clone, Hash, Serialize, Deserialize)]
pub struct PNCounter<A: Actor> {
    p: GCounter<A>,
    n: GCounter<A>,
}

impl<A: Actor> Ord for PNCounter<A> {
    fn cmp(&self, other: &PNCounter<A>) -> Ordering {
        let (c, oc) = (self.value(), other.value());
        c.cmp(&oc)
    }
}

impl<A: Actor> PartialOrd
    for PNCounter<A> {
    fn partial_cmp(&self, other: &PNCounter<A>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<A: Actor> PartialEq for PNCounter<A> {
    fn eq(&self, other: &PNCounter<A>) -> bool {
        let (c, oc) = (self.value(), other.value());
        c == oc
    }
}

impl<A: Actor> PNCounter<A> {
    /// Produces a new `PNCounter`.
    pub fn new() -> PNCounter<A> {
        PNCounter {
            p: GCounter::new(),
            n: GCounter::new(),
        }
    }

    /// Increments a particular actor's counter.
    pub fn increment(&mut self, actor: A) {
        self.p.increment(actor);
    }

    /// Decrements a particular actor's counter.
    pub fn decrement(&mut self, actor: A) {
        self.n.increment(actor);
    }

    /// Returns the current value of this counter (P-N).
    pub fn value(&self) -> i64 {
        self.p.value() as i64 - self.n.value() as i64
    }

    /// Merge another pncounter into this one, without
    /// regard to dominance.
    ///
    /// # Examples
    ///
    /// ```
    /// use crdts::PNCounter;
    /// let (mut a, mut b, mut c) = (PNCounter::new(), PNCounter::new(), PNCounter::new());
    /// a.increment("A".to_string());
    /// b.increment("B".to_string());
    /// b.increment("B".to_string());
    /// b.decrement("A".to_string());
    /// c.increment("B".to_string());
    /// c.increment("B".to_string());
    /// a.merge(b);
    /// assert_eq!(a, c);
    pub fn merge(&mut self, other: PNCounter<A>) {
        self.p.merge(other.p);
        self.n.merge(other.n);
    }
}

#[cfg(test)]
mod tests {
    extern crate rand;
    extern crate quickcheck;

    use self::quickcheck::{Arbitrary, Gen, QuickCheck, StdGen};
    use super::*;

    use std::collections::BTreeSet;

    const ACTOR_MAX: u16 = 11;
    #[derive(Debug, Clone)]
    enum Op {
        Increment(i16),
        Decrement(i16),
    }

    impl Arbitrary for Op {
        fn arbitrary<G: Gen>(g: &mut G) -> Op {
            if g.gen_weighted_bool(2) {
                Op::Increment(g.gen_range(0, ACTOR_MAX) as i16)
            } else {
                Op::Decrement(g.gen_range(0, ACTOR_MAX) as i16)
            }
        }

        fn shrink(&self) -> Box<Iterator<Item = Op>> {
            Box::new(vec![].into_iter())
        }
    }

    #[derive(Debug, Clone)]
    struct OpVec {
        ops: Vec<Op>,
    }

    impl Arbitrary for OpVec {
        fn arbitrary<G: Gen>(g: &mut G) -> OpVec {
            let mut ops = vec![];
            for _ in 0..g.gen_range(1, 100) {
                ops.push(Op::arbitrary(g));
            }
            OpVec { ops: ops }
        }

        fn shrink(&self) -> Box<Iterator<Item = OpVec>> {
            let mut smaller = vec![];
            for i in 0..self.ops.len() {
                let mut clone = self.clone();
                clone.ops.remove(i);
                smaller.push(clone);
            }

            Box::new(smaller.into_iter())
        }
    }

    fn prop_merge_converges(ops: OpVec) -> bool {
        let mut results = BTreeSet::new();

        // Permute the interleaving of operations should converge.
        // Largely taken directly from orswot
        for i in 2..ACTOR_MAX {
            let mut witnesses: Vec<PNCounter<i16>> =
                (0..i).map(|_| PNCounter::new()).collect();
            for op in ops.ops.iter() {
                match op {
                    &Op::Increment(actor) => {
                        witnesses[(actor as usize % i as usize)].increment(
                            actor,
                        );
                    }
                    &Op::Decrement(actor) => {
                        witnesses[(actor as usize % i as usize)].decrement(
                            actor,
                        );
                    }
                }
            }
            let mut merged = PNCounter::new();
            for witness in witnesses.iter() {
                merged.merge(witness.clone());
            }

            results.insert(merged.value());
            if results.len() > 1 {
                println!("opvec: {:?}", ops);
                println!("results: {:?}", results);
                println!("witnesses: {:?}", &witnesses);
                println!("merged: {:?}", merged);
            }
        }
        results.len() == 1
    }


    #[test]
    fn qc_merge_converges() {
        QuickCheck::new()
            .gen(StdGen::new(rand::thread_rng(), 1))
            .tests(1_000)
            .max_tests(10_000)
            .quickcheck(prop_merge_converges as fn(OpVec) -> bool);
    }


    #[test]
    fn test_basic() {
        let mut a = PNCounter::new();
        assert_eq!(a.value(), 0);
        a.increment("A".to_string());
        assert_eq!(a.value(), 1);
        a.increment("A".to_string());
        assert_eq!(a.value(), 2);
        a.decrement("A".to_string());
        assert_eq!(a.value(), 1);
        a.increment("A".to_string());
        assert_eq!(a.value(), 2);
    }
}
