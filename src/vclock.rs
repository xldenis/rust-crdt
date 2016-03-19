//! The `vclock` crate provides a generic vector clock implementation.
//!
//! # Examples
//!
//! ```
//! use crdt::VClock;
//! let (mut a, mut b) = (VClock::new(), VClock::new());
//! a.witness("A", 2);
//! b.witness("A", 1);
//! assert!(a > b);
//! ```

use std::cmp::{self, Ordering};
use std::collections::BTreeMap;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VClock<A: Ord>(BTreeMap<A, u64>);

impl<A: Ord> PartialOrd for VClock<A> {
    fn partial_cmp(&self, other: &VClock<A>) -> Option<Ordering> {
        if self == other {
            Some(Ordering::Equal)
        } else if other.0.iter().all(|(w, c)| self.contains_descendent_element(w, c)) {
            Some(Ordering::Greater)
        } else if self.0.iter().all(|(w, c)| other.contains_descendent_element(w, c)) {
            Some(Ordering::Less)
        } else {
            None
        }
    }
}

impl<A: Ord> VClock<A> {
    pub fn new() -> VClock<A> {
        VClock(BTreeMap::new())
    }

    /// For a particular actor, possibly store a new counter
    /// if it dominates.
    ///
    /// # Examples
    ///
    /// ```
    /// use crdt::VClock;
    /// let (mut a, mut b) = (VClock::new(), VClock::new());
    /// a.witness("A", 2);
    /// a.witness("A", 0); // ignored because 2 dominates 0
    /// b.witness("A", 1);
    /// assert!(a > b);
    /// ```
    ///
    pub fn witness(&mut self, actor: A, counter: u64) {
        if !self.contains_descendent_element(&actor, &counter) {
            self.0.insert(actor, counter);
        }
    }

    /// For a particular actor, increment the associated counter.
    ///
    /// # Examples
    ///
    /// ```
    /// use crdt::VClock;
    /// let (mut a, mut b) = (VClock::new(), VClock::new());
    /// a.increment("A");
    /// a.increment("A");
    /// a.witness("A", 0); // ignored because 2 dominates 0
    /// b.increment("A");
    /// assert!(a > b);
    /// ```
    ///
    pub fn increment(&mut self, actor: A) {
        let current = self.0.get(&actor)
                            .map(|c| *c)
                            .unwrap_or(0);
        self.0.insert(actor, current + 1);
    }

    /// Merge another vector clock into this one, without
    /// regard to dominance.
    ///
    /// # Examples
    ///
    /// ```
    /// use crdt::VClock;
    /// let (mut a, mut b, mut c) = (VClock::new(), VClock::new(), VClock::new());
    /// a.increment("A");
    /// b.increment("B");
    /// c.increment("A");
    /// c.increment("B");
    /// a.merge(b);
    /// assert!(a == c);
    /// ```
    ///
    pub fn merge(&mut self, other: VClock<A>) {
        for (w, c) in other.0.into_iter() {
            self.witness(w, c)
        }
    }

    /// Determine if a single element is present and descendent.
    /// Generally prefer using the higher-level comparison operators
    /// between vclocks over this specific method.
    #[inline]
    pub fn contains_descendent_element(&self, actor: &A, counter: &u64) -> bool {
        self.0.get(actor)
              .map(|our_counter| our_counter >= counter)
              .unwrap_or(false)
    }

    /// True if two vector clocks have diverged.
    ///
    /// # Examples
    ///
    /// ```
    /// use crdt::VClock;
    /// let (mut a, mut b) = (VClock::new(), VClock::new());
    /// a.increment("A");
    /// b.increment("B");
    /// assert!(a.concurrent(&b));
    /// ```
    pub fn concurrent(&self, other: &VClock<A>) -> bool {
        self.partial_cmp(other).is_none()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vclock_ordering() {
        assert!(VClock::<i8>::new() == VClock::new());

        let (mut a, mut b) = (VClock::new(), VClock::new());
        a.witness("A", 1);
        a.witness("A", 2);
        a.witness("A", 0);
        b.witness("A", 1);

        // a {A:2}
        // b {A:1}
        // expect: a dominates
        assert!(a > b);
        assert!(b < a);
        assert!(a != b);

        b.witness("A", 3);
        // a {A:2}
        // b {A:3}
        // expect: b dominates
        assert!(b > a);
        assert!(a < b);
        assert!(a != b);

        a.witness("B", 1);
        // a {A:2, B:1}
        // b {A:3}
        // expect: concurrent
        assert!(a != b);
        assert!(!(a > b));
        assert!(!(b > a));

        a.witness("A", 3);
        // a {A:3, B:1}
        // b {A:3}
        // expect: a dominates
        assert!(a > b);
        assert!(b < a);
        assert!(a != b);

        b.witness("B", 2);
        // a {A:3, B:1}
        // b {A:3, B:2}
        // expect: b dominates
        assert!(b > a);
        assert!(a < b);
        assert!(a != b);

        a.witness("B", 2);
        // a {A:3, B:2}
        // b {A:3, B:2}
        // expect: equal
        assert!(!(b > a));
        assert!(!(a > b));
        assert!(a == b);
    }
}
