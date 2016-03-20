//! The `orswot` crate provides an implementation of the OR-Set without tombstones (ORSWOT).
//!
//! # Examples
//!

use std::collections::BTreeMap;

use super::VClock;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, RustcEncodable, RustcDecodable)]
pub struct Orswot<Member: Ord, Actor: Ord + Clone> {
    clock: VClock<Actor>,
    entries: BTreeMap<Member, VClock<Actor>>,
    deferred: BTreeMap<VClock<Actor>, Vec<Member>>,
}

impl<Member: Ord, Actor: Ord + Clone> Orswot<Member, Actor> {
    pub fn new() -> Orswot<Member, Actor> {
        Orswot {
            clock: VClock::new(),
            entries: BTreeMap::new(),
            deferred: BTreeMap::new(),
        }
    }

    pub fn add() {}
    pub fn add_all() {}

    // drop the element out, ignoring the vclock for the element and orswot
    pub fn remove() {}
    pub fn remove_all() {}
    pub fn update() {}
    pub fn value() {}
    pub fn merge() {}
    pub fn equal() {}
    pub fn precondition_context() {}
    pub fn stats() {}
    pub fn stat() {}
    pub fn parent_clock() {}
    pub fn to_version() {}
}
