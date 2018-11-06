use std::cmp::Ordering;

use vclock::{Actor, Dot};
use gcounter::GCounter;
use traits::{CvRDT, CmRDT};

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
#[derive(Debug, Eq, Clone, Hash, Serialize, Deserialize)]
pub struct PNCounter<A: Actor> {
    p: GCounter<A>,
    n: GCounter<A>,
}

/// The Direction of an Op.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Dir {
    /// signals that the op increments the counter
    Pos,
    /// signals that the op decrements the counter
    Neg
}

/// An Op which is produced through from mutating the counter
/// Ship these ops to other replicas to have them sync up.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Op<A: Actor> {
    /// The witnessing dot for this op
    pub dot: Dot<A>,
    /// the direction to move the counter
    pub dir: Dir
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

    fn apply(&mut self, op: &Self::Op) {
        match op {
            Op { dot, dir: Dir::Pos } => self.p.apply(dot),
            Op { dot, dir: Dir::Neg } => self.n.apply(dot)
        }
    }
}

impl<A: Actor> CvRDT for PNCounter<A> {
    fn merge(&mut self, other: &Self) {
        self.p.merge(&other.p);
        self.n.merge(&other.n);
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
