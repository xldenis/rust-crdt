use serde::{Deserialize, Serialize};
use std::cmp::{Ordering, PartialOrd};
use std::hash::{Hash, Hasher};

use crate::Actor;

/// Dot is a version marker for a single actor
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Dot<A> {
    /// The actor identifier
    pub actor: A,
    /// The current version of this actor
    pub counter: u64,
}

impl<A: Actor> Dot<A> {
    /// Build a Dot from an actor and counter
    pub fn new(actor: A, counter: u64) -> Self {
        Self { actor, counter }
    }

    /// Generate the successor of this dot
    pub fn inc(&self) -> Self {
        Self {
            actor: self.actor.clone(),
            counter: self.counter + 1,
        }
    }
}

impl<A: Copy> Copy for Dot<A> {}

impl<A: PartialEq> PartialEq for Dot<A> {
    fn eq(&self, other: &Self) -> bool {
        self.actor == other.actor && self.counter == other.counter
    }
}

impl<A: Eq> Eq for Dot<A> {}

impl<A: Hash> Hash for Dot<A> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.actor.hash(state);
        self.counter.hash(state);
    }
}

impl<A: PartialOrd> PartialOrd for Dot<A> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.actor == other.actor {
            self.counter.partial_cmp(&other.counter)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_inc() {
        let dot = Dot::new(32, 1);
        assert_eq!(dot.inc(), Dot::new(32, 2));
    }

    #[test]
    fn test_partial_order() {
        let a = Dot::new(32, 1);
        let b = Dot::new(32, 2);
        let c = Dot::new(56, 1);

        assert_eq!(a.partial_cmp(&b), Some(Ordering::Less));
        assert_eq!(b.partial_cmp(&a), Some(Ordering::Greater));
        assert_eq!(a.partial_cmp(&a), Some(Ordering::Equal));
        assert_eq!(a.partial_cmp(&c), None);
    }
}
