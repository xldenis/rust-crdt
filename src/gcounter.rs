use num_bigint::BigUint;
use serde_derive::{Serialize, Deserialize};

use crate::traits::{CvRDT, CmRDT};
use crate::vclock::{VClock, Actor, Dot};

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
/// a.apply(&a.inc("A".to_string()));
/// b.apply(&b.inc("B".to_string()));
///
/// assert_eq!(a.read(), b.read());
///
/// a.apply(&a.inc("A".to_string()));
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
    /// Produce a new `GCounter`.
    pub fn new() -> Self {
        GCounter {
            inner: VClock::new(),
        }
    }

    /// Generate Op to increment the counter.
    pub fn inc(&self, actor: A) -> Dot<A> {
        self.inner.inc(actor)
    }

    /// Increment the counter.
    pub fn apply_inc(&mut self, actor: A) {
        self.inner.apply_inc(actor)
    }

    /// Return the current sum of this counter.
    pub fn read(&self) -> BigUint {
        self.inner.iter()
            .map(|dot| dot.counter)
            .sum()
    }
}
