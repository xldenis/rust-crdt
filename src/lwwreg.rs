extern crate serde;

use std::fmt::Debug;

use error::{self, Error, Result};
use traits::{FunkyCvRDT, FunkyCmRDT};

/// Trait bound alias for lwwreg vals
pub trait Val: Debug + Clone + PartialEq {}
impl<T: Debug + Clone + PartialEq> Val for T {}

/// `Marker` must grow monotonically *and* must be globally unique
pub trait Marker: Debug + Clone + Ord {}
impl<T: Debug + Clone + Ord> Marker for T {}


/// `LWWReg` is a simple CRDT that contains an arbitrary value
/// along with an `Ord` that tracks causality. It is the responsibility
/// of the user to guarantee that the source of the causal element
/// is monotonic. Don't use timestamps unless you are comfortable
/// with divergence.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LWWReg<V: Val, M: Marker> {
    /// `val` is the opaque element contained within this CRDT
    pub val: V,
    /// `marker` should be a monotonic value associated with this val
    pub marker: M,
}

impl<V: Val + Default, M: Marker + Default> Default for LWWReg<V, M> {
    fn default() -> LWWReg<V, M> {
        LWWReg {
            val: V::default(),
            marker: M::default()
        }
    }
}

impl<V: Val, M: Marker> FunkyCvRDT for LWWReg<V, M> {
    type Error = error::Error;

    /// Combines two `LWWReg` instances according to the marker that
    /// tracks causality. Returns an error if the marker is identical but the
    /// contained element is different.
    /// ```
    /// use crdts::{LWWReg, FunkyCvRDT};
    /// let mut l1 = LWWReg { val: 1, marker: 2 };
    /// let l2 = LWWReg { val: 3, marker: 2 };
    /// // errors!
    /// assert!(l1.merge(&l2).is_err());
    /// ```
    fn merge(&mut self, other: &Self) -> Result<()> {
        if other.marker > self.marker {
            self.val = other.val.clone();
            self.marker = other.marker.clone();
            Ok(())
        } else if other.marker == self.marker && other.val != self.val {
            Err(Error::ConflictingMarker)
        } else {
            Ok(())
        }
    }
}

impl<V: Val, M: Marker> FunkyCmRDT for LWWReg<V, M> {
    type Error = error::Error;
    // LWWReg's are small enough that we can replicate the entire state as an Op
    type Op = Self;

    fn apply(&mut self, op: &Self::Op) -> Result<()> {
        self.merge(op)
    }
}

impl<V: Val, M: Marker> LWWReg<V, M> {
    /// Updates value witnessed by the given marker.
    /// An Err is returned if the given marker is exactly
    /// equal to the current marker
    ///
    /// ```
    /// use crdts::LWWReg;
    /// let mut reg = LWWReg { val: 1, marker: 2 };
    ///
    /// // updating with a smaller marker is a no-op
    /// assert!(reg.update(2, 1).is_ok());
    /// assert_eq!(reg.val, 1);
    ///
    /// // updating with existing marker fails
    /// assert!(reg.update(2, 2).is_err());
    /// assert_eq!(reg, LWWReg { val: 1, marker: 2 });
    ///
    /// // updating with same val and marker succeeds
    /// assert!(reg.update(1, 2).is_ok());
    /// assert_eq!(reg, LWWReg { val: 1, marker: 2 });
    ///
    /// // updating with descendent marker succeeds
    /// assert!(reg.update(2, 3).is_ok());
    /// assert_eq!(reg, LWWReg { val: 2, marker: 3 });
    /// ```
    pub fn update(&mut self, val: V, marker: M) -> Result<()> {
        if self.marker < marker {
            self.val = val;
            self.marker = marker;
            Ok(())
        } else if self.marker == marker && val != self.val {
            Err(Error::ConflictingMarker)
        } else {
            // Either the given marker is smaller than the marker in the
            // register (meaning we've seen this update already) or the marker
            // and val are the same as is currently stored, either way:
            // this is a no-op.
            Ok(())
        }
    }
}
