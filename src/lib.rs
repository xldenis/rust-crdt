//! `crdts` is a library of thoroughly-tested, serializable CRDT's
//! ported from the riak_dt library to rust.
#![crate_type = "lib"]
#![deny(missing_docs)]

pub use vclock::VClock;
pub use orswot::Orswot;
pub use lwwreg::LWWReg;
pub use gcounter::GCounter;

/// `lwwreg` contains the last-write-wins register.
pub mod lwwreg;
/// `vclock` contains the vector clock.
pub mod vclock;
/// `orswot` contains the addition-biased or-set without tombstone.
pub mod orswot;
/// `gcounter` contains the grow-only counter
pub mod gcounter;

extern crate rustc_serialize;
extern crate bincode;
extern crate quickcheck;
extern crate rand;
#[macro_use] extern crate maplit;

use bincode::SizeLimit;
use bincode::rustc_serialize::{encode, decode, DecodingResult};
use rustc_serialize::{Encodable, Decodable};

/// Dumps this type to binary.
///
/// # Examples
///
/// ```
/// use crdts::{Orswot, to_binary, from_binary};
/// let mut a = Orswot::new();
/// a.add(1, 1);
/// let encoded = to_binary(&a);
/// let decoded = from_binary(encoded).unwrap();
/// assert_eq!(a, decoded);
/// ```
pub fn to_binary<A: Encodable>(s: &A) -> Vec<u8> {
    encode(s, SizeLimit::Infinite).unwrap()
}

/// Attempts to reconstruct a type from binary.
///
/// # Examples
///
/// ```
/// use crdts::{Orswot, to_binary, from_binary};
/// let mut a = Orswot::new();
/// a.add(1, 1);
/// let encoded = to_binary(&a);
/// let decoded = from_binary(encoded).unwrap();
/// assert_eq!(a, decoded);
/// ```
pub fn from_binary<A: Decodable>(encoded: Vec<u8>) -> DecodingResult<A> {
    decode(&encoded[..])
}
