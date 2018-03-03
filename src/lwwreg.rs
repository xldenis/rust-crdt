use super::*;

/// `LWWReg` is a simple CRDT that contains an arbitrary value
/// along with an `Ord` that tracks causality. It is the responsibility
/// of the user to guarantee that the source of the causal element
/// is monotonic. Don't use timestamps unless you are comfortable
/// with divergence.
#[serde(bound(deserialize = ""))]
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LWWReg<T, A>
where
    T: PartialEq + Serialize + DeserializeOwned,
    A: Ord + Serialize + DeserializeOwned,
{
    /// `value` is the opaque element contained within this CRDT
    pub value: T,
    /// `dot` should be a monotonic value associated with this value
    pub dot: A,
}

impl<T, A> LWWReg<T, A>
where
    T: PartialEq + Serialize + DeserializeOwned,
    A: Ord + Serialize + DeserializeOwned,
{
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
    /// let mut l1 = LWWReg { value: 1, dot: 2 };
    /// let l2 = LWWReg { value: 3, dot: 2 };
    /// // panics
    /// // l1.merge(l2);
    /// ```
    pub fn merge(&mut self, other: LWWReg<T, A>) {
        if other.dot > self.dot {
            self.value = other.value;
            self.dot = other.dot;
        } else if other.dot == self.dot && other.value != self.value {
            panic!(
                "LWWReg::merge called on elements with an identical dot but different values."
            );
        }
    }

    /// Combines two `LWWReg` instances according to the dot that
    /// tracks causality. This allows replicas to diverge if the dot
    /// is identical but the element is not.
    pub unsafe fn merge_unsafe(&mut self, other: LWWReg<T, A>) {
        if other.dot > self.dot {
            self.value = other.value;
            self.dot = other.dot;
        }
    }
}
