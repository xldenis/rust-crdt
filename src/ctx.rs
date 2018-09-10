use serde::{Serialize, de::DeserializeOwned};
use vclock::{Actor, VClock, Dot};

#[serde(bound(deserialize = ""))]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReadCtx<V: Serialize + DeserializeOwned, A: Actor> {
    pub add_clock: VClock<A>,
    pub rm_clock: VClock<A>,
    pub val: V
}

#[serde(bound(deserialize = ""))]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AddCtx<A: Actor> {
    pub(crate) clock: VClock<A>,
    pub(crate) dot: Dot<A>
}

#[serde(bound(deserialize = ""))]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RmCtx<A: Actor> {
    pub(crate) clock: VClock<A>
}

impl<V: Serialize + DeserializeOwned, A: Actor> ReadCtx<V, A> {
    pub fn derive_add_ctx(&self, actor: impl Into<A>) -> AddCtx<A> {
        let actor = actor.into();
        let mut clock = self.add_clock.clone();
        let dot = clock.inc(actor);
        clock.apply(&dot);
        AddCtx {
            clock: clock,
            dot: dot
        }
    }

    pub fn derive_rm_ctx(&self) -> RmCtx<A> {
        RmCtx {
            clock: self.rm_clock.clone()
        }
    }
}
