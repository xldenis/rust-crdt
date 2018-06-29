use serde::Serialize;
use serde::de::DeserializeOwned;

use error::Result;
use vclock::VClock;

pub trait ComposableCrdt<A>: Default where
    A : Ord + Clone + Serialize + DeserializeOwned
{
    fn set_clock(&mut self, clock: VClock<A>);
    fn merge(&mut self, other: &Self) -> Result<()>;
}
