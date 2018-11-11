//! The `orswot` crate provides an implementation of the addition-biased OR-Set
//! without tombstones (ORSWOT).  Ported directly from riak_dt.
//!
//! # Examples
//!

use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;
use std::cmp::Ordering;

use traits::{CvRDT, CmRDT, Causal};
use vclock::{VClock, Dot, Actor};
use ctx::{ReadCtx, AddCtx, RmCtx};

/// Trait bound alias for members in a set
pub trait Member: Debug + Clone + Hash + Eq {}
impl<T: Debug + Clone + Hash + Eq> Member for T {}

/// `Orswot` is an add-biased or-set without tombstones ported from
/// the riak_dt CRDT library.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Orswot<M: Member, A: Actor> {
    clock: VClock<A>,
    entries: HashMap<M, VClock<A>>,
    deferred: HashMap<VClock<A>, HashSet<M>>,
}

/// Op's define an edit to an Orswot, Op's must be replayed in the exact order
/// they were produced to guarantee convergence.
///
/// Op's are idempotent, that is, applying an Op twice will not have an effect
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Op<M: Member, A: Actor> {
    /// Add a member to the set
    Add {
        /// witnessing dot
        dot: Dot<A>,
        /// Member to add
        member: M
    },
    /// Remove a member from the set
    Rm {
        /// witnessing clock
        clock: VClock<A>,
        /// Member to remove
        member: M
    }
}

impl<M: Member, A: Actor> Default for Orswot<M, A> {
    fn default() -> Self {
        Orswot::new()
    }
}

impl<M: Member, A: Actor> CmRDT for Orswot<M, A> {
    type Op = Op<M, A>;

    fn apply(&mut self, op: &Self::Op) {
        match op.clone() {
            Op::Add { dot, member } => {
                if self.clock.get(&dot.actor) >= dot.counter {
                    // we've already seen this op
                    return;
                }
                {
                    let mut member_vclock = self.entries.entry(member)
                        .or_default();

                    member_vclock.apply(&dot);
                }
                self.clock.apply(&dot);
                self.apply_deferred();
            },
            Op::Rm { clock, member } => {
                self.apply_remove(member, &clock);
            }
        }
    }
}

impl<M: Member, A: Actor> CvRDT for Orswot<M, A> {
    /// Merge combines another `Orswot` with this one.
    fn merge(&mut self, other: &Self) {
        let mut other_remaining = other.entries.clone();
        let mut keep = HashMap::new();
        for (entry, mut clock) in self.entries.clone().into_iter() {
            match other.entries.get(&entry).cloned() {
                None => {
                    // other doesn't contain this entry because it:
                    //  1. has witnessed it and dropped it
                    //  2. hasn't witnessed it
                    if clock <= other.clock {
                        // other has seen this entry and dropped it
                    } else {
                        // other has not seen this entry, so add it
                        keep.insert(entry, clock);
                    }
                }
                Some(mut other_entry_clock) => {
                    // SUBTLE: this entry is present in both orswots, BUT that doesn't mean we
                    // shouldn't drop it!

                    let mut common = clock.intersection(&other_entry_clock);
                    clock.subtract(&common);
                    other_entry_clock.subtract(&common);
                    clock.subtract(&other.clock);
                    other_entry_clock.subtract(&self.clock);

                    common.merge(&clock);
                    common.merge(&other_entry_clock);

                    // Perfectly possible that an item present in both sets
                    // is dropped
                    if common.is_empty() {
                        // we should drop, there are no common dots
                    } else {
                        // we should not drop, as there are common clocks
                        keep.insert(entry.clone(), common);
                    }
                    // don't want to consider this again below
                    other_remaining.remove(&entry).unwrap();
                }
            }
        }

        for (entry, mut clock) in other_remaining.into_iter() {
            clock.subtract(&self.clock);
            if !clock.is_empty() {
                // other has witnessed a novel addition, so add it
                keep.insert(entry, clock);
            }
        }

        // merge deferred removals
        for (clock, deferred) in other.deferred.iter() {
            let mut our_deferred =
                self.deferred.remove(&clock).unwrap_or_default();
            for e in deferred.iter() {
                our_deferred.insert(e.clone());
            }
            self.deferred.insert(clock.clone(), our_deferred);
        }

        self.entries = keep;

        // merge vclocks
        self.clock.merge(&other.clock);

        self.apply_deferred();
    }
}

impl<M: Member, A: Actor> Causal<A> for Orswot<M, A> {
    fn truncate(&mut self, clock: &VClock<A>) {
        // TODO: this is kinda lazy, improve this
        let mut empty_set = Orswot::new();
        empty_set.clock = clock.clone();

        self.merge(&empty_set);
        self.clock.subtract(&clock);

        for (_, member_clock) in self.entries.iter_mut() {
            member_clock.subtract(&clock);
        }
    }
}

impl<M: Member, A: Actor> Orswot<M, A> {
    /// Returns a new `Orswot` instance.
    pub fn new() -> Self {
        Orswot {
            clock: VClock::new(),
            entries: HashMap::new(),
            deferred: HashMap::new(),
        }
    }

    /// Add a single element.
    pub fn add(&self, member: impl Into<M>, ctx: AddCtx<A>) -> Op<M, A> {
        Op::Add { dot: ctx.dot, member: member.into() }
    }

    /// Remove a member with a witnessing ctx.
    pub fn remove(&self, member: impl Into<M>, ctx: RmCtx<A>) -> Op<M, A> {
        Op::Rm { clock: ctx.clock, member: member.into() }
    }

    /// Remove a member using a witnessing clock.
    fn apply_remove(&mut self, member: impl Into<M>, clock: &VClock<A>) {
        let member: M = member.into();
        match clock.partial_cmp(&self.clock) {
            None | Some(Ordering::Greater) => {
                let mut deferred_drops = self.deferred
                    .remove(&clock)
                    .unwrap_or_default();
                deferred_drops.insert(member.clone());
                self.deferred.insert(clock.clone(), deferred_drops);
            }
            _ => {/* we've already seen this remove */}
        }

        if let Some(mut existing_clock) = self.entries.remove(&member) {
            existing_clock.subtract(&clock);
            if !existing_clock.is_empty() {
                self.entries.insert(member.clone(), existing_clock);
            }
        }
    }

    /// Check if the set contains a member
    pub fn contains(&self, member: &M) -> ReadCtx<bool, A> {
        let member_clock_opt = self.entries.get(&member);
        let exists = member_clock_opt.is_some();
        ReadCtx {
            add_clock: self.clock.clone(),
            rm_clock: member_clock_opt
                .cloned()
                .unwrap_or_default(),
            val: exists
        }
    }

    /// Retrieve the current members.
    pub fn read(&self) -> ReadCtx<HashSet<M>, A> {
        ReadCtx {
            add_clock: self.clock.clone(),
            rm_clock: self.clock.clone(),
            val: self.entries.keys().cloned().collect()
        }
    }

    fn apply_deferred(&mut self) {
        let deferred = self.deferred.clone();
        self.deferred = HashMap::new();
        for (clock, entries) in deferred.into_iter() {
            entries.into_iter()
                .map(|member| self.apply_remove(member, &clock))
                .collect()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    extern crate rand;

    #[test]
    // a bug found with rust quickcheck where deferred operations
    // are not carried over after a merge.
    // symptoms:
    //  if nothing is added, it works
    //  if removed elem is added first, it only misses one
    //  if non-related elem is added, it misses both
    fn ensure_deferred_merges() {
        let (mut a, mut b) = (Orswot::<String, u8>::new(), Orswot::<String, u8>::new());

        let b_read_ctx = b.read();
        let b_op1 = b.add("element 1", b_read_ctx.derive_add_ctx(5));
        b.apply(&b_op1);

        // remove with a future context
        let rm_op1 = b.remove("element 1", RmCtx { clock: Dot { actor: 5, counter: 4 }.into() });
        b.apply(&rm_op1);
        
        let a_read_ctx = a.read();
        let a_op = a.add("element 4", a_read_ctx.derive_add_ctx(6));
        a.apply(&a_op);
        
        // remove with a future context
        let rm_op2 = b.remove("element 9", RmCtx { clock: Dot { actor: 4, counter: 4 }.into() });
        b.apply(&rm_op2);

        let mut merged = Orswot::new();
        merged.merge(&a);
        merged.merge(&b);
        merged.merge(&Orswot::new());
        assert_eq!(merged.deferred.len(), 2);
    }

    // a bug found with rust quickcheck where deferred removals
    // were not properly preserved across merges.
    #[test]
    fn preserve_deferred_across_merges() {
        let mut a = Orswot::<u8, u8>::new();
        let mut b = a.clone();
        let mut c = a.clone();

        // add element 5 from witness 1
        let op = a.add(5, a.read().derive_add_ctx(1));
        a.apply(&op);

        // on another clock, remove 5 with an advanced clock for witnesses 1 and 4
        let mut vc = VClock::new();
        vc.apply_dot(Dot::new(1, 3));
        vc.apply_dot(Dot::new(4, 8));

        // remove from b (has not yet seen add for 5) with advanced ctx
        let rm_op = b.remove(5, RmCtx { clock: vc });
        b.apply(&rm_op);
        assert_eq!(b.deferred.len(), 1);

        // ensure that the deferred elements survive across a merge
        c.merge(&b);
        assert_eq!(c.deferred.len(), 1);

        // after merging the set with deferred elements with the set that contains
        // an inferior member, ensure that the member is no longer visible and
        // the deferred set still contains this info
        a.merge(&c);
        assert!(a.read().val.is_empty());
    }

    // port from riak_dt
    // Bug found by EQC, not dropping dots in merge when an element is
    // present in both Sets leads to removed items remaining after merge.
    #[test]
    fn test_present_but_removed() {
        let mut a = Orswot::<u8, String>::new();
        let mut b = Orswot::<u8, String>::new();
        let a_add_ctx = a.read()
            .derive_add_ctx("A".to_string());
        let a_op = a.add(0, a_add_ctx);
        a.apply(&a_op);
        // Replicate it to C so A has 0->{a, 1}
        let c = a.clone();

        let rm_op = a.remove(0, a.contains(&0).derive_rm_ctx());
        a.apply(&rm_op);
        assert_eq!(a.deferred.len(), 0);

        let b_add_ctx = b.read()
            .derive_add_ctx("B".to_string());
        let b_op = b.add(0, b_add_ctx);
        b.apply(&b_op);

        // Replicate B to A, so now A has a 0
        // the one with a Dot of {b,1} and clock
        // of [{a, 1}, {b, 1}]
        a.merge(&b);

        let rm_op = b.remove(0, b.contains(&0).derive_rm_ctx());
        b.apply(&rm_op);
        // Both C and A have a '0', but when they merge, there should be
        // no '0' as C's has been removed by A and A's has been removed by
        // C.
        a.merge(&b);
        a.merge(&c);
        println!("{:#?}", a);
        assert!(a.read().val.is_empty());
    }
}
