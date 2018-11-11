use traits::{CvRDT, CmRDT};
use vclock::{VClock, Actor, Dot};

/// `GCounter` is a grow-only witnessed counter.
///
/// # Examples
///
/// ```
/// use crdts::{GCounter, CmRDT};
/// 
/// let mut a = GCounter::new();
/// let mut b = GCounter::new();
///
/// let op_a1 = a.inc("A".to_string());
/// let op_b = b.inc("B".to_string());
/// a.apply(&op_a1);
/// b.apply(&op_b);
/// assert_eq!(a.read(), b.read());
/// let op_a2 = a.inc("A".to_string());
/// a.inc("A".to_string());
/// a.apply(&op_a2);
/// assert!(a.read() > b.read());
/// ```
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub struct GCounter<A: Actor> {
    inner: VClock<A>,
}

impl<A: Actor> Default for GCounter<A> {
    fn default() -> Self {
        GCounter::new()
    }
}

impl<A: Actor> CmRDT for GCounter<A> {
    type Op = Dot<A>;

    fn apply(&mut self, op: &Self::Op) {
        self.inner.apply(op)
    }
}

impl<A: Actor> CvRDT for GCounter<A> {
    fn merge(&mut self, other: &Self) {
        self.inner.merge(&other.inner);
    }
}

impl<A: Actor> GCounter<A> {
    /// Produces a new `GCounter`.
    pub fn new() -> Self {
        GCounter { inner: VClock::new() }
    }

    /// Generate Op to increment the counter.
    pub fn inc(&self, actor: A) -> Dot<A> {
        self.inner.inc(actor)
    }

    /// Increment the counter.
    pub fn apply_inc(&mut self, actor: A) {
        self.inner.apply_inc(actor)
    }

    /// Returns the current sum of this counter.
    pub fn read(&self) -> u64 {
        self.inner.iter()
            .map(|dot| dot.counter)
            .sum()
    }
}
