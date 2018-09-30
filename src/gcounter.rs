use std::cmp::Ordering;
use traits::{CvRDT, CmRDT};
use vclock::{VClock, Actor, Dot};

/// `GCounter` is a grow-only witnessed counter.
///
/// # Examples
///
/// ```
/// use crdts::{GCounter, CmRDT};
/// 
/// let (mut a, mut b) = (GCounter::new(), GCounter::new());
/// let op_a1 = a.inc("A".to_string());
/// let op_b = b.inc("B".to_string());
/// a.apply(&op_a1);
/// b.apply(&op_b);
/// assert_eq!(a.value(), b.value());
/// assert!(a == b);
/// let op_a2 = a.inc("A".to_string());
/// a.inc("A".to_string());
/// a.apply(&op_a2);
/// assert!(a > b);
/// ```
#[serde(bound(deserialize = ""))]
#[derive(Debug, Eq, Clone, Hash, Serialize, Deserialize)]
pub struct GCounter<A: Actor> {
    inner: VClock<A>,
}

impl<A: Actor> Ord for GCounter<A> {
    fn cmp(&self, other: &GCounter<A>) -> Ordering {
        let (c, oc) = (self.value(), other.value());
        c.cmp(&oc)
    }
}

impl<A: Actor> PartialOrd for GCounter<A> {
    fn partial_cmp(&self, other: &GCounter<A>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<A: Actor> PartialEq for GCounter<A> {
    fn eq(&self, other: &GCounter<A>) -> bool {
        let (c, oc) = (self.value(), other.value());
        c == oc
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
    pub fn new() -> GCounter<A> {
        GCounter { inner: VClock::new() }
    }

    /// Increment the counter.
    pub fn inc(&self, actor: A) -> Dot<A> {
        self.inner.inc(actor)
    }

    /// Returns the current sum of this counter.
    pub fn value(&self) -> u64 {
        self.inner.dots.values().fold(0, |acc, count| acc + count)
    }
}
