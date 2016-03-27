//! The `orswot` crate provides an implementation of the addition-biased OR-Set
//! without tombstones (ORSWOT).  Ported directly from riak_dt.
//!
//! # Examples
//!

use std::collections::{BTreeMap, BTreeSet};

use super::VClock;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Orswot<Member: Ord + Clone, Actor: Ord + Clone> {
    clock: VClock<Actor>,
    entries: BTreeMap<Member, VClock<Actor>>,
    deferred: BTreeMap<VClock<Actor>, BTreeSet<Member>>,
}

impl<Member: Ord + Clone, Actor: Ord + Clone> Orswot<Member, Actor> {
    pub fn new() -> Orswot<Member, Actor> {
        Orswot {
            clock: VClock::new(),
            entries: BTreeMap::new(),
            deferred: BTreeMap::new(),
        }
    }

    /// Add a single element.
    pub fn add(&mut self, member: Member, actor: Actor) {
        // TODO(tyler) is this
        let counter = self.clock.increment(actor.clone());

        let mut entry_clock = VClock::new();
        entry_clock.witness(actor, counter).unwrap();

        self.entries.insert(member, entry_clock);
    }

    /// Add several members.
    pub fn add_all(&mut self, members: Vec<Member>, actor: Actor) {
        for member in members.into_iter() {
            self.add(member, actor.clone());
        }
    }

    /// Remove a member without providing a witnessing context.
    /// Returns an existing context `VClock` if it was present.
    pub fn remove(&mut self, member: Member) -> Option<VClock<Actor>> {
        self.entries.remove(&member)
    }

    /// Remove a member using a witnessing context.
    pub fn remove_with_context(&mut self, member: Member,
                               context: &VClock<Actor>) {
        if *context > self.clock {
            let mut deferred_drops = self.deferred.remove(context).unwrap_or(BTreeSet::new());
            deferred_drops.insert(member.clone());
            self.deferred.insert(context.clone(), deferred_drops);
        }

        if let Some(existing_context) = self.entries.remove(&member) {
            let dom_clock = existing_context.dominating_vclock(context.clone());
            if !dom_clock.is_empty() {
                self.entries.insert(member, dom_clock);
            }
        }
    }

    /// Remove multiple members, without providing a witnessing context.
    pub fn remove_all(&mut self, members: Vec<Member>) -> Vec<Option<VClock<Actor>>> {
        members.into_iter().map(|member| self.remove(member)).collect()
    }

    /// Remove multiple members with a witnessing context.
    pub fn remove_all_with_context(&mut self,
                                   members: Vec<Member>,
                                   context: &VClock<Actor>) {
        for member in members.into_iter() {
            self.remove_with_context(member, context);
        }
    }

    /// Retrieve the current members.
    pub fn value(&self) -> Vec<Member> {
        self.entries.keys().cloned().collect()
    }

    /// Merge combines another `Orswot` with this one.
    ///
    pub fn merge(&mut self, mut other: Orswot<Member, Actor>) {
        let mut keep = BTreeMap::new();
        for (entry, clock) in self.entries.clone().into_iter() {
            if !other.entries.contains_key(&entry) {
                // other doesn't contain this entry because it:
                //  1. has witnessed it and dropped it
                //  2. hasn't witnessed it
                if clock.dominating_vclock(other.clock.clone()).is_empty() {
                    // the other orswot has witnessed the entry's clock, and dropped this entry
                } else {
                    // the other orswot has not witnessed this add, so add it
                    keep.insert(entry, clock);
                }
            } else {
                // SUBTLE: this entry is present in both orswots, BUT that doesn't mean we
                // shouldn't drop it!
                let common = clock.intersection(other.clone().clock);
                let luniq = clock.dominating_vclock(common.clone());
                let runiq = other.clone().clock.dominating_vclock(common.clone());
                let lkeep = luniq.dominating_vclock(other.clone().clock);
                let rkeep = runiq.dominating_vclock(self.clone().clock);
                // Perfectly possible that an item in both sets should be dropped
                let mut common = common;
                common.merge(lkeep);
                common.merge(rkeep);
                if !common.is_empty() {
                    // we should not drop, as there are common clocks
                } else {
                    keep.insert(entry.clone(), clock);
                }
                // don't want to consider this again below
                other.entries.remove(&entry).unwrap();
            }
        }

        for (entry, clock) in other.entries.clone().into_iter() {
            let dom_clock = clock.dominating_vclock(self.clock.clone());
            if !dom_clock.is_empty() {
                // other has witnessed a novel addition, so add it
                keep.insert(entry, dom_clock);
            }
        }

        // merge deferred removals
        for (clock, mut deferred) in self.deferred.iter_mut() {
            let other_deferred = other.deferred.remove(clock).unwrap_or(BTreeSet::new());
            for e in other_deferred.into_iter() {
                deferred.insert(e);
            }
        }

        self.entries = keep;

        // merge vclocks
        self.clock.merge(other.clone().clock);

        self.apply_deferred();
    }

    fn apply_deferred(&mut self) {
        let deferred = self.deferred.clone();
        self.deferred = BTreeMap::new();
        for (clock, entries) in deferred.into_iter() {
            self.remove_all_with_context(entries.into_iter().collect(), &clock);
        }
    }

    pub fn precondition_context(&self) -> VClock<Actor> {
        self.clock.clone()
    }
}

#[cfg(test)]
mod tests {
    extern crate quickcheck;
    extern crate rand;

    use self::quickcheck::{Arbitrary, Gen, Testable, QuickCheck, StdGen};
    use self::rand::Rng;

    use super::*;

    // TODO(tyler) perform quickchecking a la https://github.com/basho/riak_dt/blob/develop/src/riak_dt_orswot.erl#L625
    // port from riak_dt
    #[test]
    fn test_disjoint_merge() {
        let (mut a, mut b) = (Orswot::new(), Orswot::new());
        a.add("bar".to_string(), "A".to_string());
        assert_eq!(a.value(), vec!["bar".to_string()]);
        b.add("baz".to_string(), "B".to_string());
        assert_eq!(b.value(), vec!["baz".to_string()]);
        let mut c = a.clone();
        assert_eq!(c.value(), vec!["bar".to_string()]);
        c.merge(b);
        assert_eq!(c.value(), vec!["bar".to_string(), "baz".to_string()]);
        a.remove("bar".to_string());
        let mut d = a.clone();
        d.merge(c);
        assert_eq!(d.value(), vec!["baz".to_string()]);
    }

    // port from riak_dt
    // Bug found by EQC, not dropping dots in merge when an element is
    // present in both Sets leads to removed items remaining after merge.
    #[test]
    fn test_present_but_removed() {
        let (mut a, mut b) = (Orswot::new(), Orswot::new());
        a.add("Z".to_string(), "A".to_string());
        // Replicate it to C so A has 'Z'->{e, 1}
        let c = a.clone();
        a.remove("Z".to_string());
        b.add("Z".to_string(), "B".to_string());
        // Replicate B to A, so now A has a Z, the one with a Dot of
        // {b,1} and clock of [{a, 1}, {b, 1}]
        a.merge(b.clone());
        b.remove("Z".to_string());
        // Both C and A have a 'Z', but when they merge, there should be
        // no 'Z' as C's has been removed by A and A's has been removed by
        // C.
        a.merge(b);
        a.merge(c);
        assert!(a.value().is_empty());
    }

    // port from riak_dt
    // A bug EQC found where dropping the dots in merge was not enough if
    // you then store the value with an empty clock (derp).
    #[test]
    fn test_no_dots_left_test() {
        let (mut a, mut b) = (Orswot::new(), Orswot::new());
        a.add("Z".to_string(), 1);
        b.add("Z".to_string(), 2);
        let c = a.clone();
        a.remove("Z".to_string());
        // replicate B to A, now A has B's 'Z'
        a.merge(b.clone());
        assert_eq!(a.value(), vec!["Z".to_string()]);
        b.remove("Z".to_string());
        assert!(b.value().is_empty());
        // Replicate C to B, now B has A's old 'Z'
        b.merge(c);
        assert_eq!(b.value(), vec!["Z".to_string()]);
        // Merge everytyhing, without the fix You end up with 'Z' present,
        // with no dots
        a.merge(b);
        assert!(a.value().is_empty());
    }

    // port from riak_dt
    // A test I thought up
    // - existing replica of ['A'] at a and b,
    // - add ['B'] at b, but not communicated to any other nodes, context returned to client
    // - b goes down forever
    // - remove ['A'] at a, using the context the client got from b
    // - will that remove happen?
    //   case for shouldn't: the context at b will always be bigger than that at a
    //   case for should: we have the information in dots that may allow us to realise it can be removed
    //     without us caring.
    //
    // as the code stands, 'A' *is* removed, which is almost certainly correct. This behaviour should
    // always happen, but may not. (ie, the test needs expanding)
    #[test]
    fn test_dead_node_update() {
        let mut a = Orswot::new();
        a.add("A".to_string(), 1);
        let mut b = a.clone();
        b.add("B".to_string(), 2);
        let bctx = b.precondition_context();
        a.remove_with_context("A".to_string(), &bctx);
        assert!(a.value().is_empty());
    }
}
