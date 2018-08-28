use std::cmp::Ordering;

use vclock::{Actor, Dot};
use gcounter::GCounter;
use traits::{CvRDT, CmRDT};
use error::{Result, Error};

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
/// use crdts::{PNCounter, CmRDT};
///
/// let mut a = PNCounter::new();
/// let op1 = a.inc("A".to_string());
/// a.apply(&op1);
/// let op2 = a.inc("A".to_string());
/// a.apply(&op2);
/// let op3 = a.dec("A".to_string());
/// a.apply(&op3);
/// let op4 = a.inc("A".to_string());
/// a.apply(&op4);
///
/// assert_eq!(a.value(), 2);
/// ```
#[serde(bound(deserialize = ""))]
#[derive(Debug, Eq, Clone, Hash, Serialize, Deserialize)]
pub struct PNCounter<A: Actor> {
    p: GCounter<A>,
    n: GCounter<A>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum Dir {
    Pos,
    Neg
}

/// An Op which is produced through from mutating the counter
/// Ship these ops to other replicas to have them sync up.
#[serde(bound(deserialize = ""))]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Op<A: Actor> {
    dot: Dot<A>,
    dir: Dir
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

impl<A: Actor> CmRDT for PNCounter<A> {
    type Op = Op<A>;
    type Error = Error;

    fn apply(&mut self, op: &Self::Op) -> Result<()> {
        match op {
            Op { dot, dir: Dir::Pos } => self.p.apply(dot),
            Op { dot, dir: Dir::Neg } => self.n.apply(dot)
        }
    }
}

impl<A: Actor> CvRDT for PNCounter<A> {
    type Error = Error;

    fn merge(&mut self, other: &Self) -> Result<()> {
        self.p.merge(&other.p)?;
        self.n.merge(&other.n)
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
    pub fn inc(&self, actor: A) -> Op<A> {
        Op { dot: self.p.inc(actor), dir: Dir::Pos }
    }

    /// Decrements a particular actor's counter.
    pub fn dec(&self, actor: A) -> Op<A> {
        Op { dot: self.n.inc(actor), dir: Dir::Neg }
    }

    /// Returns the current value of this counter (P-N).
    pub fn value(&self) -> i64 {
        self.p.value() as i64 - self.n.value() as i64
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

    impl Arbitrary for Op<i16> {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            let actor = g.gen_range(0, ACTOR_MAX) as i16;
            let counter = g.gen_range(0, 200);
            let dot = Dot { actor, counter };
            
            let dir = if g.gen_weighted_bool(2) {
                Dir::Pos
            } else {
                Dir::Neg
            };

            Op { dot, dir }
        }

        fn shrink(&self) -> Box<Iterator<Item = Self>> {
            Box::new(vec![].into_iter())
        }
    }

    #[derive(Debug, Clone)]
    struct OpVec {
        ops: Vec<Op<i16>>,
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
                let index = op.dot.actor as usize % i as usize;
                let witness = &mut witnesses[index];
                witness.apply(op).unwrap();
            }
            let mut merged = PNCounter::new();
            for witness in witnesses.iter() {
                merged.merge(&witness).unwrap();
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

        let op1 = a.inc("A".to_string());
        a.apply(&op1).unwrap();
        assert_eq!(a.value(), 1);

        let op2 = a.inc("A".to_string());
        a.apply(&op2).unwrap();
        assert_eq!(a.value(), 2);

        let op3 = a.dec("A".to_string());
        a.apply(&op3).unwrap();
        assert_eq!(a.value(), 1);

        let op4 = a.inc("A".to_string());
        a.apply(&op4).unwrap();
        assert_eq!(a.value(), 2);
    }
}
