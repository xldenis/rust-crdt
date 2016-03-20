#![crate_id = "crdt"]
#![crate_type = "lib"]

pub use vclock::VClock;
pub use orswot::Orswot;

pub mod lwwreg;
pub mod vclock;
pub mod orswot;

extern crate rustc_serialize;
extern crate bincode;
