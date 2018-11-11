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
/// a.apply_inc("A".to_string());
/// a.apply_inc("A".to_string());
/// a.apply_dec("A".to_string());
/// a.apply_inc("A".to_string());
///
/// assert_eq!(a.read(), 2);
/// ```
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
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

impl<A: Actor> Default for PNCounter<A> {
    fn default() -> Self {
        PNCounter::new()
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
    pub fn new() -> Self {
        PNCounter {
            p: GCounter::new(),
            n: GCounter::new(),
        }
    }

    /// Generate an Op to increment the counter.
    pub fn inc(&self, actor: A) -> Op<A> {
        Op { dot: self.p.inc(actor), dir: Dir::Pos }
    }

    /// Generate an Op to increment the counter.
    pub fn dec(&self, actor: A) -> Op<A> {
        Op { dot: self.n.inc(actor), dir: Dir::Neg }
    }

    /// Increments counter.
    pub fn apply_inc(&mut self, actor: A) {
        self.p.apply_inc(actor)
    }

    /// Decrements counter.
    pub fn apply_dec(&mut self, actor: A) {
        self.n.apply_inc(actor)
    }

    /// Returns the current value of this counter (P-N).
    pub fn read(&self) -> i64 {
        (i128::from(self.p.read()) - i128::from(self.n.read())) as i64
    }
}
