use std::cmp::{Ordering};

use rustc_serialize::{Encodable, Decodable};

use super::VClock;

/// `GCounter` is a grow-only witnessed counter.
///
/// # Examples
///
/// ```
/// use crdts::GCounter;
/// let (mut a, mut b) = (GCounter::new(), GCounter::new());
/// a.increment("A".to_string());
/// b.increment("B".to_string());
/// assert_eq!(a.value(), b.value());
/// assert!(a == b);
/// a.increment("A".to_string());
/// assert!(a > b);
/// ```
#[derive(Debug, Eq, Clone, Hash, RustcEncodable, RustcDecodable)]
pub struct GCounter<A: Ord + Clone + Encodable + Decodable> {
    inner: VClock<A>
}

impl<A: Ord + Clone + Encodable + Decodable> Ord for GCounter<A> {
    fn cmp(&self, other: &GCounter<A>) -> Ordering {
        let (c, oc) = (self.value(), other.value());
        c.cmp(&oc)
    }
}

impl<A: Ord + Clone + Encodable + Decodable> PartialOrd for GCounter<A> {
    fn partial_cmp(&self, other: &GCounter<A>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<A: Ord + Clone + Encodable + Decodable> PartialEq for GCounter<A> {
    fn eq(&self, other: &GCounter<A>) -> bool {
        let (c, oc) = (self.value(), other.value());
        c == oc
    }
}

impl<A: Ord + Clone + Encodable + Decodable> GCounter<A> {
    /// Produces a new `GCounter`.
    pub fn new() -> GCounter<A> {
        GCounter {
            inner: VClock::new()
        }
    }

    /// Increments a particular actor's counter.
    pub fn increment(&mut self, actor: A) {
        self.inner.increment(actor);
    }

    /// Returns the current sum of this counter.
    pub fn value(&self) -> u64 {
        self.inner.dots.values().fold(0, |acc, count| acc + count)
    }

    /// Merge another gcounter into this one, without
    /// regard to dominance.
    ///
    /// # Examples
    ///
    /// ```
    /// use crdts::GCounter;
    /// let (mut a, mut b, mut c) = (GCounter::new(), GCounter::new(), GCounter::new());
    /// a.increment("A".to_string());
    /// b.increment("B".to_string());
    /// c.increment("A".to_string());
    /// c.increment("B".to_string());
    /// a.merge(b);
    /// assert_eq!(a, c);
    pub fn merge(&mut self, other: GCounter<A>) {
        self.inner.merge(other.inner);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic() {
        let (mut a, mut b) = (GCounter::new(), GCounter::new());
        a.increment("A".to_string());
        b.increment("B".to_string());
        assert_eq!(a.value(), b.value());
        assert!(a == b);
        a.increment("A".to_string());
        assert!(a > b);
    }
}

