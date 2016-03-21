//! The `orswot` crate provides an implementation of the OR-Set without tombstones (ORSWOT).
//!
//! # Examples
//!

use std::collections::BTreeMap;

use super::VClock;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Ord, PartialOrd, RustcEncodable, RustcDecodable)]
pub struct Orswot<Member: Ord + Clone, Actor: Ord + Clone> {
    clock: VClock<Actor>,
    entries: BTreeMap<Member, VClock<Actor>>,
    deferred: BTreeMap<VClock<Actor>, Vec<Member>>,
}

impl<Member: Ord + Clone, Actor: Ord + Clone> Orswot<Member, Actor> {
    pub fn new() -> Orswot<Member, Actor> {
        Orswot {
            clock: VClock::new(),
            entries: BTreeMap::new(),
            deferred: BTreeMap::new(),
        }
    }

    pub fn add(&mut self, member: Member, actor: Actor) {
        let counter = self.clock.increment(actor.clone());

        // TODO(tyler) riak_dt doesn't merge entry clocks on add.  Is this a bug?
        let mut entry_clock = VClock::new();
        entry_clock.witness(actor, counter).unwrap();

        self.entries.insert(member, entry_clock);
    }

    pub fn add_all(&mut self, members: Vec<(Member, Actor)>) {
        members.into_iter().map(|(member, actor)| self.add(member, actor));
    }

    // drop the element out, ignoring the vclock for the element and orswot
    pub fn remove(&mut self, member: Member) -> Option<VClock<Actor>> {
        self.entries.remove(&member)
    }

    pub fn remove_all(&mut self, members: Vec<Member>) -> Vec<Option<VClock<Actor>>> {
        members.into_iter().map(|member| self.remove(member)).collect()
    }

    pub fn value(&self) -> Vec<Member> {
        self.entries.keys().cloned().collect()
    }

    pub fn merge(&mut self, other: Orswot<Member, Actor>) {
        self.clock.merge(other.clock);
    }

    fn merge_deferred(&mut self, deferred: BTreeMap<VClock<Actor>, Vec<Member>>) {}
    pub fn equal() {}
    pub fn precondition_context() {}
    pub fn stats() {}
    pub fn stat() {}
    pub fn parent_clock() {}
    pub fn to_version() {}
}
