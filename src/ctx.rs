use serde::{Serialize, de::DeserializeOwned};
use vclock::{Actor, VClock, Dot};

#[serde(bound(deserialize = ""))]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReadCtx<V: Serialize + DeserializeOwned, A: Actor> {
    pub clock: VClock<A>,
    pub val: V
}

#[serde(bound(deserialize = ""))]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WriteCtx<A: Actor> {
    pub(crate) clock: VClock<A>,
    pub(crate) dot: Dot<A>
}

impl<V: Serialize + DeserializeOwned, A: Actor> ReadCtx<V, A> {
    pub fn derive_write_ctx(&self, actor: impl Into<A>) -> WriteCtx<A> {
        let actor = actor.into();
        let mut clock = self.clock.clone();
        let dot = clock.inc(actor);
        clock.apply(&dot);
        WriteCtx {
            clock: clock,
            dot: dot
        }
    }
}
