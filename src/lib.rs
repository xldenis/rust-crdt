//! A pure-Rust library of thoroughly-tested, serializable CRDT's.
//!
//! [Conflict-free Replicated Data Types][crdt] (CRDTs) are data structures
//! which can be replicated across multiple networked nodes, and whose
//! properties allow for deterministic, local resolution of
//! possible inconsistencies which might result from concurrent
//! operations.
//!
//! [crdt]: https://en.wikipedia.org/wiki/Conflict-free_replicated_data_type
#![crate_type = "lib"]
#![deny(missing_docs)]

mod error;
pub use crate::error::Error;

mod traits;
pub use crate::traits::{Causal, CmRDT, CvRDT, FunkyCmRDT, FunkyCvRDT};

/// This module contains a Last-Write-Wins Register.
pub mod lwwreg;

/// This module contains a Multi-Value Register.
pub mod mvreg;

pub mod vclock;

/// This module contains an Observed-Remove Set With Out Tombstones.
pub mod orswot;

/// This module contains a Grow-only Counter.
pub mod gcounter;

/// This module contains a Grow-only Set.
pub mod gset;

/// This module contains a Positive-Negative Counter.
pub mod pncounter;

/// This module contains a Map with Reset-Remove and Observed-Remove semantics.
pub mod map;

/// This module contains context for editing a CRDT.
pub mod ctx;

/// This module contains a Sequence.
pub mod lseq;

// Top-level re-exports for CRDT structures.
pub use crate::{
    gcounter::GCounter,
    gset::GSet,
    lwwreg::LWWReg,
    map::Map,
    mvreg::MVReg,
    orswot::Orswot,
    pncounter::PNCounter,
    vclock::{Dot, VClock},
};
