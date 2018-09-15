//! The `vclock` crate provides a generic vector clock implementation.
//!
//! # Examples
//!
//! ```
//! use crdts::VClock;
//! let (mut a, mut b) = (VClock::new(), VClock::new());
//! a.witness("A".to_string(), 2);
//! b.witness("A".to_string(), 1);
//! assert!(a > b);
//! ```

// TODO: we have a mixture of language here with witness and actor. Clean this up

use super::*;

use std::fmt::{self, Debug, Display};
use std::cmp::{self, Ordering};
use std::collections::{BTreeMap, btree_map};
use std::hash::Hash;

/// A counter is used to track causality at a particular actor.
pub type Counter = u64;

/// Common Actor type, Actors are unique identifier for every `thing` mutating a VClock.
/// VClock based CRDT's will need to expose this Actor type to the user.
pub trait Actor: Ord + Clone + Hash + Send + Serialize + DeserializeOwned + Debug {}
impl<A: Ord + Clone + Hash + Send + Serialize + DeserializeOwned + Debug> Actor for A {}


/// Dot is a version marker for a single actor
#[serde(bound(deserialize = ""))]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Dot<A: Actor> {
    /// The actor identifier
    pub actor: A,
    /// The current version of this actor
    pub counter: Counter
}

// TODO: VClock derives an Ord implementation, but a total order over VClocks doesn't exist. I think this may mess up our BTreeMap usage in ORSWOT and friends

/// A `VClock` is a standard vector clock.
/// It contains a set of "actors" and associated counters.
/// When a particular actor witnesses a mutation, their associated
/// counter in a `VClock` is incremented. `VClock` is typically used
/// as metadata for associated application data, rather than as the
/// container for application data. `VClock` just tracks causality.
/// It can tell you if something causally descends something else,
/// or if different replicas are "concurrent" (were mutated in
/// isolation, and need to be resolved externally).
#[serde(bound(deserialize = ""))]
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct VClock<A: Actor> {
    /// dots is the mapping from actors to their associated counters
    pub dots: BTreeMap<A, Counter>,
}

impl<A: Actor> PartialOrd for VClock<A> {
    fn partial_cmp(&self, other: &VClock<A>) -> Option<Ordering> {
        if self == other {
            Some(Ordering::Equal)
        } else if other.dots.iter().all(|(w, c)| &self.get(w) >= c) {
            Some(Ordering::Greater)
        } else if self.dots.iter().all(|(w, c)| &other.get(w) >= c) {
            Some(Ordering::Less)
        } else {
            None
        }
    }
}

impl<A: Actor + Display> Display for VClock<A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(")?;
        for (i, (actor, count)) in self.dots.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}->{}", actor, count)?;
        }
        write!(f, ")")
    }
}

impl<A: Actor> Causal<A> for VClock<A> {
    /// Truncates to the greatest-lower-bound of the given VClock and self
    /// ``` rust
    /// use crdts::{VClock, Causal};
    /// let mut c = VClock::new();
    /// c.witness(23, 6);
    /// c.witness(89, 14);
    /// let c2 = c.clone();
    ///
    /// c.truncate(&c2); // should be a no-op
    /// assert_eq!(c, c2);
    ///
    /// c.witness(43, 1);
    /// assert_eq!(c.get(&43), 1);
    /// c.truncate(&c2); // should remove the 43 => 1 entry
    /// assert_eq!(c.get(&43), 0);
    /// ```
    fn truncate(&mut self, other: &VClock<A>) {
        let mut actors_to_remove: Vec<A> = Vec::new();
        for (actor, count) in self.dots.iter_mut() {
            let min_count = cmp::min(*count, other.get(actor));
            if min_count > 0 {
                *count = min_count
            } else {
                // Since an actor missing from the dots map has an implied counter of 0
                // we can save some memory, and remove the actor.
                actors_to_remove.push(actor.clone())
            }
        }

        // finally, remove all the zero counter actor
        for actor in actors_to_remove {
            self.dots.remove(&actor);
        }
    }
}

impl<A: Actor> CmRDT for VClock<A> {
    type Op = Dot<A>;

    fn apply(&mut self, dot: &Self::Op) {
        let _ = self.witness(dot.actor.clone(), dot.counter);
    }
}

impl<A: Actor> CvRDT for VClock<A> {
    fn merge(&mut self, other: &VClock<A>) {
        for (actor, counter) in other.dots.iter() {
            let _ = self.witness(actor.clone(), *counter);
        }
    }
}

impl<A: Actor> VClock<A> {
    /// Returns a new `VClock` instance.
    pub fn new() -> VClock<A> {
        VClock { dots: BTreeMap::new() }
    }

    /// For a particular actor, possibly store a new counter
    /// if it dominates.
    ///
    /// # Examples
    ///
    /// ```
    /// use crdts::VClock;
    /// let (mut a, mut b) = (VClock::new(), VClock::new());
    /// a.witness("A".to_string(), 2);
    /// a.witness("A".to_string(), 0); // ignored because 2 dominates 0
    /// b.witness("A".to_string(), 1);
    /// assert!(a > b);
    /// ```
    ///
    pub fn witness(&mut self, actor: A, counter: Counter) -> Result<()> {
        if !(self.get(&actor) >= counter) {
            self.dots.insert(actor, counter);
            Ok(())
        } else {
            Err(Error::ConflictingDot)
        }
    }

    /// For a particular actor, increment the associated counter.
    ///
    /// # Examples
    ///
    /// ```
    /// use crdts::{VClock, CmRDT};
    /// let (mut a, mut b) = (VClock::new(), VClock::new());
    /// let a_op1 = a.inc("A".to_string());
    /// a.apply(&a_op1);
    /// let a_op2 = a.inc("A".to_string());
    /// a.apply(&a_op2);
    ///
    /// a.witness("A".to_string(), 0); // ignored because 2 dominates 0
    /// let b_op = b.inc("A".to_string());
    /// b.apply(&b_op);
    /// assert!(a > b);
    /// ```
    pub fn inc(&self, actor: A) -> Dot<A> {
        let next = self.get(&actor) + 1;
        Dot { actor: actor, counter: next }
    }

    /// True if two vector clocks have diverged.
    ///
    /// # Examples
    ///
    /// ```
    /// use crdts::{VClock, CmRDT};
    /// let (mut a, mut b) = (VClock::new(), VClock::new());
    /// let a_op = a.inc("A".to_string());
    /// a.apply(&a_op);
    /// let b_op = b.inc("B".to_string());
    /// b.apply(&b_op);
    /// assert!(a.concurrent(&b));
    /// ```
    pub fn concurrent(&self, other: &VClock<A>) -> bool {
        self.partial_cmp(other).is_none()
    }

    /// Return the associated counter for this actor.
    /// All actors not in the vclock have an implied count of 0
    pub fn get(&self, actor: &A) -> Counter {
        self.dots.get(actor)
            .map(|counter| *counter)
            .unwrap_or(0)
    }

    /// Returns `true` if this vector clock contains nothing.
    pub fn is_empty(&self) -> bool {
        self.dots.is_empty()
    }

    /// Returns the common elements (same actor and counter)
    /// for two `VClock` instances.
    pub fn intersection(&self, other: &VClock<A>) -> VClock<A> {
        let mut dots = BTreeMap::new();
        for (actor, counter) in self.dots.iter() {
            let other_counter = other.get(actor);
            if other_counter == *counter {
                dots.insert(actor.clone(), *counter);
            }
        }
        VClock { dots: dots }
    }

    /// Returns an iterator over the dots in this vclock
    pub fn iter(&self) -> impl Iterator<Item=(&A, &u64)> {
        self.dots.iter()
    }

    /// Forget actors who appear in the given VClock with descendent dots
    pub fn subtract(&mut self, other: &VClock<A>) {
        for (actor, counter) in other.iter() {
            if counter >= &self.get(&actor) {
                self.dots.remove(&actor);
            }
        }
    }
}

impl<A: Actor> std::iter::IntoIterator for VClock<A> {
    type Item = (A, u64);
    type IntoIter = btree_map::IntoIter<A, u64>;
    
    /// Consumes the vclock and returns an iterator over dots in the clock
    fn into_iter(self) -> btree_map::IntoIter<A, u64> {
        self.dots.into_iter()
    }
}

impl<A: Actor> std::iter::FromIterator<(A, u64)> for VClock<A> {
    fn from_iter<I: IntoIterator<Item=(A, u64)>>(iter: I) -> Self {
        let mut clock = Self::new();

        for (actor, counter) in iter {
            let _ = clock.witness(actor, counter);
        }

        clock
    }
}

impl<A: Actor> From<Vec<(A, u64)>> for VClock<A> {
    fn from(vec: Vec<(A, u64)>) -> Self {
        vec.into_iter().collect()
    }
}

impl<A: Actor> From<Dot<A>> for VClock<A> {
    fn from(dot: Dot<A>) -> Self {
        let mut clock = VClock::new();
        let _ = clock.witness(dot.actor, dot.counter);
        clock
    }
}

#[cfg(test)]
mod tests {
    extern crate rand;
    extern crate quickcheck;

    use self::quickcheck::{Arbitrary, Gen};
    use super::*;

    impl<A: Actor + Arbitrary> Arbitrary for VClock<A> {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            let mut v = VClock::new();
            for _ in 0..g.gen_range(0, 7) {
                let witness = A::arbitrary(g);
                let _ = v.witness(witness, g.gen_range(1, 7));
            }
            v
        }

        fn shrink(&self) -> Box<Iterator<Item = VClock<A>>> {
            let mut smaller = vec![];
            for k in self.dots.keys() {
                let mut vc = self.clone();
                vc.dots.remove(k);
                smaller.push(vc)
            }
            Box::new(smaller.into_iter())
        }
    }

    quickcheck! {
        fn prop_from_iter_of_iter_is_nop(clock: VClock<u8>) -> bool {
            clock == clock.clone().into_iter().collect()
        }

        fn prop_from_iter_order_of_dots_should_not_matter(dots: Vec<(u8, u64)>) -> bool {
            // TODO: is there a better way to check comutativity of dots?
            let reverse: VClock<u8> = dots.clone()
                .into_iter()
                .rev()
                .collect();
            let forward: VClock<u8> = dots
                .into_iter()
                .collect();

            reverse == forward
        }

        fn prop_from_iter_dots_should_be_idempotent(dots: Vec<(u8, u64)>) -> bool {
            let single: VClock<u8> = dots.clone()
                .into_iter()
                .collect();

            let double: VClock<u8> = dots.clone()
                .into_iter()
                .chain(dots.into_iter())
                .collect();

            single == double
        }

        fn prop_truncate_self_is_nop(clock: VClock<u8>) -> bool {
            let mut clock_truncated = clock.clone();
            clock_truncated.truncate(&clock);

            clock_truncated == clock
        }

        fn prop_subtract_with_empty_is_nop(clock: VClock<u8>) -> bool {
            let mut subbed  = clock.clone();
            subbed.subtract(&VClock::new());
            subbed == clock
        }

        fn prop_subtract_self_is_empty(clock: VClock<u8>) -> bool {
            let mut subbed  = clock.clone();
            subbed.subtract(&clock);
            subbed == VClock::new()
        }
    }

    #[test]
    fn test_subtract() {
        let mut a: VClock<u8> = vec![(1, 4), (2, 3), (5, 9)].into_iter().collect();
        let     b: VClock<u8> = vec![(1, 5), (2, 3), (5, 8)].into_iter().collect();
        let expected: VClock<u8> = vec![(5, 9)].into_iter().collect();

        a.subtract(&b);

        assert_eq!(a, expected);
    }

    #[test]
    fn test_merge() {
        let mut a: VClock<u8> = vec![(1, 1), (2, 2), (4, 4)].into_iter().collect();
        let b: VClock<u8> = vec![(3, 3), (4, 3)].into_iter().collect();
        a.merge(&b);
        
        let c: VClock<u8> = vec![(1, 1), (2, 2), (3, 3), (4, 4)].into_iter().collect();
        assert_eq!(a, c);
    }

    #[test]
    fn test_merge_less_left() {
        let (mut a, mut b) = (VClock::new(), VClock::new());
        a.witness(5, 5).unwrap();

        b.witness(6, 6).unwrap();
        b.witness(7, 7).unwrap();

        a.merge(&b);
        assert_eq!(a.get(&5), 5);
        assert_eq!(a.get(&6), 6);
        assert_eq!(a.get(&7), 7);
    }

    #[test]
    fn test_merge_less_right() {
        let (mut a, mut b) = (VClock::new(), VClock::new());
        a.witness(6, 6).unwrap();
        a.witness(7, 7).unwrap();

        b.witness(5, 5).unwrap();

        a.merge(&b);
        assert_eq!(a.get(&5), 5);
        assert_eq!(a.get(&6), 6);
        assert_eq!(a.get(&7), 7);
    }

    #[test]
    fn test_merge_same_id() {
        let (mut a, mut b) = (VClock::new(), VClock::new());
        a.witness(1, 1).unwrap();
        a.witness(2, 1).unwrap();

        b.witness(1, 1).unwrap();
        b.witness(3, 1).unwrap();

        a.merge(&b);
        assert_eq!(a.get(&1), 1);
        assert_eq!(a.get(&2), 1);
        assert_eq!(a.get(&3), 1);
    }

    #[test]
    fn test_vclock_ordering() {
        assert_eq!(VClock::<i8>::new(), VClock::new());

        let (mut a, mut b) = (VClock::new(), VClock::new());
        a.witness("A".to_string(), 1).unwrap();
        a.witness("A".to_string(), 2).unwrap();
        assert!(a.witness("A".to_string(), 0).is_err());
        b.witness("A".to_string(), 1).unwrap();

        // a {A:2}
        // b {A:1}
        // expect: a dominates
        assert!(a > b);
        assert!(b < a);
        assert!(a != b);

        b.witness("A".to_string(), 3).unwrap();
        // a {A:2}
        // b {A:3}
        // expect: b dominates
        assert!(b > a);
        assert!(a < b);
        assert!(a != b);

        a.witness("B".to_string(), 1).unwrap();
        // a {A:2, B:1}
        // b {A:3}
        // expect: concurrent
        assert!(a != b);
        assert!(!(a > b));
        assert!(!(b > a));

        a.witness("A".to_string(), 3).unwrap();
        // a {A:3, B:1}
        // b {A:3}
        // expect: a dominates
        assert!(a > b);
        assert!(b < a);
        assert!(a != b);

        b.witness("B".to_string(), 2).unwrap();
        // a {A:3, B:1}
        // b {A:3, B:2}
        // expect: b dominates
        assert!(b > a);
        assert!(a < b);
        assert!(a != b);

        a.witness("B".to_string(), 2).unwrap();
        // a {A:3, B:2}
        // b {A:3, B:2}
        // expect: equal
        assert!(!(b > a));
        assert!(!(a > b));
        assert_eq!(a, b);
    }
}
