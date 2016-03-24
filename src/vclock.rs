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

pub type Counter = u64;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Ord, RustcEncodable, RustcDecodable)]
pub struct VClock<A: Ord + Clone> {
    dots: BTreeMap<A, Counter>
}

impl<A: Ord + Clone> PartialOrd for VClock<A> {
    fn partial_cmp(&self, other: &VClock<A>) -> Option<Ordering> {
        if self == other {
            Some(Ordering::Equal)
        } else if other.dots.iter().all(|(w, c)| self.contains_descendent_element(w, c)) {
            Some(Ordering::Greater)
        } else if self.dots.iter().all(|(w, c)| other.contains_descendent_element(w, c)) {
            Some(Ordering::Less)
        } else {
            None
        }
    }
}

impl<A: Ord + Clone> VClock<A> {
    pub fn new() -> VClock<A> {
        VClock {
            dots: BTreeMap::new()
        }
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
    pub fn witness(&mut self, actor: A, counter: Counter) -> Result<(), ()> {
        if !self.contains_descendent_element(&actor, &counter) {
            self.dots.insert(actor, counter);
            Ok(())
        } else {
            Err(())
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
    pub fn increment(&mut self, actor: A) -> Counter {
        let next = self.dots.get(&actor)
                            .map(|c| *c)
                            .unwrap_or(0) + 1;
        self.dots.insert(actor, next);
        next
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
        for (w, c) in other.dots.into_iter() {
            self.witness(w, c);
        }
    }

    /// Determine if a single element is present and descendent.
    /// Generally prefer using the higher-level comparison operators
    /// between vclocks over this specific method.
    #[inline]
    pub fn contains_descendent_element(&self, actor: &A, counter: &Counter) -> bool {
        self.dots.get(actor)
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

    /// Return the associated counter for this actor, if present.
    pub fn get_counter(&self, actor: &A) -> Option<Counter> {
        self.dots.get(actor).map(|counter| *counter)
    }

    /// Return the difference in dots between self and a provided dots map.
    pub fn subtract_dots(&self, dots: BTreeMap<A, Counter>) -> BTreeMap<A, Counter> {
        let mut ret = BTreeMap::new();
        for (actor, counter) in self.dots.iter() {
            let other = dots.get(actor).map(|c| *c).unwrap_or(0);
            let diff = counter - other;
            if diff > 0 {
                ret.insert(actor.clone(), diff);
            }
        }
        ret
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vclock_ordering() {
        assert!(VClock::<i8>::new() == VClock::new());

        let (mut a, mut b) = (VClock::new(), VClock::new());
        a.witness("A", 1).unwrap();
        a.witness("A", 2).unwrap();
        assert!(a.witness("A", 0).is_err());
        b.witness("A", 1).unwrap();

        // a {A:2}
        // b {A:1}
        // expect: a dominates
        assert!(a > b);
        assert!(b < a);
        assert!(a != b);

        b.witness("A", 3).unwrap();
        // a {A:2}
        // b {A:3}
        // expect: b dominates
        assert!(b > a);
        assert!(a < b);
        assert!(a != b);

        a.witness("B", 1).unwrap();
        // a {A:2, B:1}
        // b {A:3}
        // expect: concurrent
        assert!(a != b);
        assert!(!(a > b));
        assert!(!(b > a));

        a.witness("A", 3).unwrap();
        // a {A:3, B:1}
        // b {A:3}
        // expect: a dominates
        assert!(a > b);
        assert!(b < a);
        assert!(a != b);

        b.witness("B", 2).unwrap();
        // a {A:3, B:1}
        // b {A:3, B:2}
        // expect: b dominates
        assert!(b > a);
        assert!(a < b);
        assert!(a != b);

        a.witness("B", 2).unwrap();
        // a {A:3, B:2}
        // b {A:3, B:2}
        // expect: equal
        assert!(!(b > a));
        assert!(!(a > b));
        assert!(a == b);
    }
}
