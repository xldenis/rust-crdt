use serde::Serialize;
use serde::de::DeserializeOwned;

use error::Result;
use vclock::VClock;

/// ComposableCrdt's can be nested into other CRDT's like Map
pub trait ComposableCrdt<A>: Default where
    A : Ord + Clone + Serialize + DeserializeOwned
{
    /// set the vclock of the crdt (if one exists) to the one passed in
    fn set_clock(&mut self, clock: VClock<A>);

    /// merge the other CRDT into this CRDT.
    fn merge(&mut self, other: &Self) -> Result<()>;
}
