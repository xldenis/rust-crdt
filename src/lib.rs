//! `crdts` is a library of thoroughly-tested, serializable CRDT's
//! ported from the riak_dt library to rust.
#![crate_type = "lib"]
#![deny(missing_docs)]

mod traits;

/// This module contains a Last-Write-Wins Register
pub mod lwwreg;

/// This module contains a Multi-Value Register
pub mod mvreg;

/// This module contains a Vector Clock
pub mod vclock;

/// This module contains an Observed-Remove Set with out tombstones
pub mod orswot;

/// This module contains a Grow-only counter
pub mod gcounter;

/// This module contains a postive-negative counter
pub mod pncounter;

/// This module contains a Map with Reset-Remove and Observed-Remove semantics
pub mod map;

/// This module contains context for editing a CRDT
pub mod ctx;
mod error;

pub use crate::{
    error::Error,
    gcounter::GCounter,
    lwwreg::LWWReg,
    mvreg::MVReg,
    orswot::Orswot,
    pncounter::PNCounter,
    map::Map,
    ctx::{ReadCtx, AddCtx, RmCtx},
    vclock::{VClock, Dot, Actor},
    traits::{CvRDT, CmRDT, Causal, FunkyCvRDT, FunkyCmRDT}
};
