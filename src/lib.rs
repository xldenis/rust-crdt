#![crate_type = "lib"]

pub use vclock::VClock;
pub use orswot::Orswot;

pub mod lwwreg;
pub mod vclock;
pub mod orswot;

extern crate rustc_serialize;
extern crate bincode;
extern crate quickcheck;
extern crate rand;

use bincode::SizeLimit;
use bincode::rustc_serialize::{encode, decode, DecodingResult};
use rustc_serialize::{Encodable, Decodable};

/// Dumps this type to binary.
pub fn to_binary<A: Encodable>(s: &A) -> Vec<u8> {
    encode(s, SizeLimit::Infinite).unwrap()
}

/// Attempts to reconstruct a type from binary.
pub fn from_binary<A: Decodable>(encoded: Vec<u8>) -> DecodingResult<A> {
    decode(&encoded[..])
}
