extern crate serde;

use std::fmt::Debug;

use serde::Serialize;
use serde::de::DeserializeOwned;

use error::{self, Error, Result};
use traits::{CvRDT, CmRDT};

/// Trait bound alias for lwwreg vals
pub trait Val: Debug + Clone + PartialEq + Send + Serialize + DeserializeOwned {}
impl<T: Debug + Clone + PartialEq + Send + Serialize + DeserializeOwned> Val for T {}

/// Trait bound alias for lwwreg dots
pub trait Dot: Debug + Clone + Ord + Send + Serialize + DeserializeOwned {}
impl<T: Debug + Clone + Ord + Send + Serialize + DeserializeOwned> Dot for T {}


/// `LWWReg` is a simple CRDT that contains an arbitrary value
/// along with an `Ord` that tracks causality. It is the responsibility
/// of the user to guarantee that the source of the causal element
/// is monotonic. Don't use timestamps unless you are comfortable
/// with divergence.
#[serde(bound(deserialize = ""))]
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LWWReg<V: Val, D: Dot> {
    /// `val` is the opaque element contained within this CRDT
    pub val: V,
    /// `dot` should be a monotonic value associated with this val
    pub dot: D,
}

impl<V: Val + Default, D: Dot + Default> Default for LWWReg<V, D> {
    fn default() -> LWWReg<V, D> {
        LWWReg {
            val: V::default(),
            dot: D::default()
        }
    }
}

impl<V: Val, D: Dot> CvRDT for LWWReg<V, D> {
    type Error = error::Error;

    /// Combines two `LWWReg` instances according to the dot that
    /// tracks causality. Panics if the dot is identical but the
    /// contained element is different. If you would prefer divergence,
    /// use `merge_unsafe` below.
    ///
    /// #Panics
    /// `merge` will panic if passed a `LWWReg` instance with an
    /// identical dot but different element, indicating a breach
    /// of monotonicity.
    ///
    /// ```
    /// use crdts::LWWReg;
    /// let mut l1 = LWWReg { val: 1, dot: 2 };
    /// let l2 = LWWReg { val: 3, dot: 2 };
    /// // panics
    /// // l1.merge(l2);
    /// ```
    fn merge(&mut self, other: &Self) -> Result<()> {
        if other.dot > self.dot {
            self.val = other.val.clone();
            self.dot = other.dot.clone();
            Ok(())
        } else if other.dot == self.dot && other.val != self.val {
            Err(Error::ConflictingDot)
        } else {
            Ok(())
        }
    }
}

impl<V: Val, D: Dot> CmRDT for LWWReg<V, D> {
    type Error = error::Error;
    // LWWReg's are small enough that we can replicate the entire state as an Op
    type Op = Self;

    fn apply(&mut self, op: &Self::Op) -> Result<()> {
        self.merge(op)
    }
}

impl<V: Val, D: Dot> LWWReg<V, D> {
    /// Updates value witnessed by the given dot.
    /// An Err is returned if the given dot is exactly
    /// equal to the current dot
    ///
    /// ```
    /// use crdts::LWWReg;
    /// let mut reg = LWWReg { val: 1, dot: 2 };
    ///
    /// // updating with a smaller dot is a no-op
    /// assert!(reg.update(2, 1).is_ok());
    /// assert_eq!(reg.val, 1);
    ///
    /// // updating with existing dot fails
    /// assert!(reg.update(2, 2).is_err());
    /// assert_eq!(reg, LWWReg { val: 1, dot: 2 });
    ///
    /// // updating with same val and dot succeeds
    /// assert!(reg.update(1, 2).is_ok());
    /// assert_eq!(reg, LWWReg { val: 1, dot: 2 });
    ///
    /// // updating with descendent dot succeeds
    /// assert!(reg.update(2, 3).is_ok());
    /// assert_eq!(reg, LWWReg { val: 2, dot: 3 });
    /// ```
    pub fn update(&mut self, val: V, dot: D) -> Result<()> {
        if self.dot < dot {
            self.val = val;
            self.dot = dot;
            Ok(())
        } else if self.dot == dot && val != self.val {
            Err(Error::ConflictingDot)
        } else {
            // Either the given dot is smaller than the dot in the
            // register (meaning we've seen this update already) or the dot
            // and val are the same as is currently stored, either way:
            // this is a no-op.
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate rand;

    use quickcheck::{Arbitrary, Gen, TestResult};
    use super::*;

    /// We need to make sure that we don't generate two LWWReg's that
    /// use the same dot but with a different value.
    ///
    /// To get around this, we include the val in the dot.
    impl<V: Val + Arbitrary, D: Dot + Arbitrary> Arbitrary for LWWReg<V, D> {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            let val = V::arbitrary(g);
            let dot = D::arbitrary(g);
            LWWReg { val, dot }
        }

        fn shrink(&self) -> Box<Iterator<Item = Self>> {
            Box::new(vec![].into_iter())
        }
    }
    
    #[test]
    fn test_default() {
        let reg: LWWReg<String, u64> = LWWReg::default();

        assert_eq!(reg, LWWReg { val: "".to_string(), dot: 0});
    }

    #[test]
    fn test_update() {
        let mut reg = LWWReg {val: 123, dot: 0};

        // normal update: new dot is a descended of current dot
        // EXPECTED: success, the val and dot are update
        assert!(reg.update(32, 2).is_ok());
        assert_eq!(reg, LWWReg {val: 32, dot: 2});

        // stale update: new dot is an ancester of the current dot
        // EXPECTED: succes, no-op
        assert!(reg.update(57, 1).is_ok());
        assert_eq!(reg, LWWReg {val: 32, dot: 2});

        // redundant update: new dot and val is same as of the current state
        // EXPECTED: success, no-op
        assert!(reg.update(32, 2).is_ok());
        assert_eq!(reg, LWWReg {val: 32, dot: 2});

        // bad update: new dot same as of the current dot but not value
        // EXPECTED: error
        assert_eq!(reg.update(4000, 2), Err(Error::ConflictingDot));
        assert_eq!(reg, LWWReg {val: 32, dot: 2});
    }

    quickcheck! {
        fn prop_associative(
            r1: LWWReg<u16, (u16, u16)>,
            r2: LWWReg<u16, (u16, u16)>,
            r3: LWWReg<u16, (u16, u16)>
        ) -> TestResult {
            let has_conflicting_dot = (r1.dot == r2.dot && r1.val != r2.val)
                || (r1.dot == r3.dot && r1.val != r3.val)
                || (r2.dot == r3.dot && r2.val != r3.val);
            if has_conflicting_dot {
                return TestResult::discard();
            }
            // we need mutation
            let mut r1 = r1;
            let mut r2 = r2;
            let mut r1_snapshot = r1.clone();

            // (r1 ^ r2) ^ r3
            assert!(r1.merge(&r2).is_ok());
            assert!(r1.merge(&r3).is_ok());

            // r1 ^ (r2 ^ r3)
            assert!(r2.merge(&r3).is_ok());
            assert!(r1_snapshot.merge(&r2).is_ok());
            
            // (r1 ^ r2) ^ r3 = r1 ^ (r2 ^ r3)
            TestResult::from_bool(r1 == r1_snapshot)
        }
        
        fn prop_commutative(
            r1: LWWReg<u16, (u16, u16)>,
            r2: LWWReg<u16, (u16, u16)>
        ) -> TestResult {
            if r1.dot == r2.dot && r1.val != r2.val {
                return TestResult::discard();
            }
            let mut r1 = r1;
            let mut r2 = r2;
            let r1_snapshot = r1.clone();

            // r1 ^ r2
            assert!(r1.merge(&r2).is_ok());

            // r2 ^ r1
            assert!(r2.merge(&r1_snapshot).is_ok());

            // r1 ^ r2 = r2 ^ r1
            TestResult::from_bool(r1 == r2)
        }

        fn prop_idempotent(r: LWWReg<u16, (u16, u16)>) -> bool {
            let mut r = r;
            let r_snapshot = r.clone();

            // r ^ r
            assert!(r.merge(&r_snapshot).is_ok());
            // r ^ r = r
            r == r_snapshot
        }
    }
}
