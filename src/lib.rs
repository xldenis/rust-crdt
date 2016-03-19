#![crate_id = "crdt"]
#![crate_type = "lib"]

pub use vclock::VClock;

pub mod lwwreg;
pub mod vclock;

extern crate rustc_serialize;
