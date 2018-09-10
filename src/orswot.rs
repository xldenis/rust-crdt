//! The `orswot` crate provides an implementation of the addition-biased OR-Set
//! without tombstones (ORSWOT).  Ported directly from riak_dt.
//!
//! # Examples
//!

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Debug;

use serde::Serialize;
use serde::de::DeserializeOwned;

use traits::{CvRDT, CmRDT, Causal};
use vclock::{VClock, Dot, Actor};
use ctx::{ReadCtx, AddCtx, RmCtx};

/// Trait bound alias for members in a set
pub trait Member: Debug + Ord + Clone + Send + Serialize + DeserializeOwned {}
impl<T: Debug + Ord + Clone + Send + Serialize + DeserializeOwned> Member for T {}

/// `Orswot` is an add-biased or-set without tombstones ported from
/// the riak_dt CRDT library.
#[serde(bound(deserialize = ""))]
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Orswot<M: Member, A: Actor> {
    clock: VClock<A>,
    entries: BTreeMap<M, VClock<A>>,
    deferred: BTreeMap<VClock<A>, BTreeSet<M>>,
}

/// Op's define a mutation to a Orswot, Op's must be replayed in the exact order
/// they were produced to guarantee convergence.
///
/// Op's are idempotent, that is, applying an Op twice will not have an effect
#[serde(bound(deserialize = ""))]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Op<M: Member, A: Actor> {
    /// Add a member to the set
    Add {
        /// Add witnessing dot
        dot: Dot<A>,
        /// Member to add
        member: M
    },
    /// Remove a member from the set
    Rm {
        /// Remove witnessing clock
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
                        .or_insert_with(|| VClock::new());

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
        let mut keep = BTreeMap::new();
        for (entry, clock) in self.entries.clone().into_iter() {
            match other.entries.get(&entry) {
                None => {
                    // other doesn't contain this entry because it:
                    //  1. has witnessed it and dropped it
                    //  2. hasn't witnessed it
                    if clock.dominating_vclock(&other.clock).is_empty() {
                        // the other orswot has witnessed the entry's clock, and dropped this entry
                    } else {
                        // the other orswot has not witnessed this add, so add it
                        keep.insert(entry, clock);
                    }
                }
                Some(other_entry_clock) => {
                    // SUBTLE: this entry is present in both orswots, BUT that doesn't mean we
                    // shouldn't drop it!
                    let common = clock.intersection(&other_entry_clock);
                    let luniq = clock.dominating_vclock(&common);
                    let runiq = other_entry_clock.dominating_vclock(&common);
                    let lkeep = luniq.dominating_vclock(&other.clock);
                    let rkeep = runiq.dominating_vclock(&self.clock);
                    // Perfectly possible that an item in both sets should be dropped
                    let mut common = common;
                    common.merge(&lkeep);
                    common.merge(&rkeep);
                    if common.is_empty() {
                        // we should not drop, as there are common clocks
                    } else {
                        keep.insert(entry.clone(), common);
                    }
                    // don't want to consider this again below
                    other_remaining.remove(&entry).unwrap();
                }
            }
        }

        for (entry, clock) in other_remaining.into_iter() {
            let dom_clock = clock.dominating_vclock(&self.clock);
            if !dom_clock.is_empty() {
                // other has witnessed a novel addition, so add it
                keep.insert(entry, dom_clock);
            }
        }

        // merge deferred removals
        for (clock, deferred) in other.deferred.iter() {
            let mut our_deferred =
                self.deferred.remove(&clock).unwrap_or(BTreeSet::new());
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
            entries: BTreeMap::new(),
            deferred: BTreeMap::new(),
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
        if !clock.dominating_vclock(&self.clock).is_empty() {
            let mut deferred_drops =
                self.deferred.remove(&clock).unwrap_or_else(|| BTreeSet::new());
            deferred_drops.insert(member.clone());
            self.deferred.insert(clock.clone(), deferred_drops);
        }

        if let Some(existing_clock) = self.entries.remove(&member) {
            let dom_clock = existing_clock.dominating_vclock(&clock);
            if !dom_clock.is_empty() {
                self.entries.insert(member.clone(), dom_clock);
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
                .unwrap_or_else(|| VClock::new()),
            val: exists
        }
    }

    /// Retrieve the current members.
    pub fn value(&self) -> ReadCtx<Vec<M>, A> {
        ReadCtx {
            add_clock: self.clock.clone(),
            rm_clock: self.clock.clone(),
            val: self.entries.keys().cloned().collect()
        }
    }

    fn apply_deferred(&mut self) {
        let deferred = self.deferred.clone();
        self.deferred = BTreeMap::new();
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

    use quickcheck::{Arbitrary, Gen, QuickCheck, StdGen};

    const ACTOR_MAX: u16 = 11;

    // TODO(tyler) perform quickchecking a la https://github.com/basho/riak_dt/blob/develop/src/riak_dt_orswot.erl#L625
    #[derive(Debug, Clone)]
    enum Op {
        Add { member: u16, actor: u16 },
        Remove {
            member: u16,
            actor: u16,
            ctx: Option<VClock<u16>>,
        },
    }

    impl Arbitrary for Op {
        fn arbitrary<G: Gen>(g: &mut G) -> Op {
            if g.gen_weighted_bool(2) {
                Op::Add {
                    member: g.gen_range(0, ACTOR_MAX),
                    actor: g.gen_range(0, ACTOR_MAX),
                }
            } else {
                // HACK always provide a ctx with removals to
                // bypass non-deterministic removal behavior when
                // omitting it.
                let ctx = if g.gen_weighted_bool(1) {
                    Some(VClock::arbitrary(g))
                } else {
                    None
                };

                Op::Remove {
                    member: g.gen_range(0, ACTOR_MAX),
                    actor: g.gen_range(0, ACTOR_MAX),
                    ctx: ctx,
                }
            }
        }

        fn shrink(&self) -> Box<Iterator<Item = Op>> {
            match self {
                &Op::Remove {
                    ctx: Some(ref ctx),
                    member,
                    actor,
                } => {
                    Box::new(ctx.shrink().map(move |c| {
                        Op::Remove {
                            ctx: Some(c),
                            member: member,
                            actor: actor,
                        }
                    }))
                }
                _ => Box::new(vec![].into_iter()),
            }
        }
    }

    #[derive(Debug, Clone)]
    struct OpVec {
        ops: Vec<Op>,
    }

    impl Arbitrary for OpVec {
        fn arbitrary<G: Gen>(g: &mut G) -> OpVec {
            let mut ops = vec![];
            let mut seen_adds = BTreeSet::new();
            for _ in 0..g.gen_range(1, 100) {
                let op = Op::arbitrary(g);
                // here we make sure an element is only added
                // once, to force determinism in the face of
                // behavior shown in `weird_highlight_4` below
                match op.clone() {
                    Op::Add { member, .. } => {
                        if !seen_adds.contains(&member) {
                            seen_adds.insert(member.clone());
                            ops.push(op);
                        }
                    }
                    _ => {
                        ops.push(op);
                    }
                }

            }
            OpVec { ops: ops }
        }

        fn shrink(&self) -> Box<Iterator<Item = OpVec>> {
            let mut smaller = vec![];
            for i in 0..self.ops.len() {
                let mut clone = self.clone();
                clone.ops.remove(i);
                smaller.push(clone);
            }

            Box::new(smaller.into_iter())
        }
    }

    fn prop_merge_converges(ops: OpVec) -> bool {
        // Different interleavings of ops applied to different
        // orswots should all converge when merged. Apply the
        // ops to increasing numbers of witnessing orswots,
        // then merge them together and make sure they have
        // all converged.
        let mut results = BTreeSet::new();
        for i in 2..ACTOR_MAX {
            let mut witnesses: Vec<Orswot<u16, u16>> =
                (0..i).map(|_| Orswot::new()).collect();
            for op in ops.ops.iter() {
                match op {
                    &Op::Add { member, actor } => {
                        let witness = &mut witnesses[(actor % i) as usize];
                        let read_ctx = witness.value();
                        let op = witness.add(member, read_ctx.derive_add_ctx(actor));
                        witness.apply(&op);
                    }
                    &Op::Remove {
                        ctx: None,
                        member,
                        actor,
                    } => {
                        let witness = &mut witnesses[(actor % i) as usize];
                        let read_ctx = witness.value();
                        let op = witness
                            .remove(member, read_ctx.derive_rm_ctx());
                        witness.apply(&op);
                    },
                    &Op::Remove {
                        ctx: Some(ref ctx),
                        member,
                        actor,
                    } => {
                        let witness = &mut witnesses[(actor % i) as usize];
                        witness.apply_remove(member, ctx);
                    }
                }
            }
            let mut merged = Orswot::new();
            for witness in witnesses.iter() {
                merged.merge(&witness);
            }

            // defer_plunger is used to merge deferred elements from the above.
            // to illustrate why this is needed, check out `weird_highlight_3`
            // below.
            let defer_plunger = Orswot::new();
            merged.merge(&defer_plunger);

            results.insert(merged.value().val);
            if results.len() > 1 {
                println!("opvec: {:?}", ops);
                println!("results: {:?}", results);
                println!("witnesses: {:?}", &witnesses);
                println!("merged: {:?}", merged);
            }
        }
        results.len() == 1
    }

    #[test]
    //#[ignore]
    fn qc_merge_converges() {
        QuickCheck::new()
            .gen(StdGen::new(rand::thread_rng(), 1))
            .tests(100)
            .max_tests(10_000)
            .quickcheck(prop_merge_converges as fn(OpVec) -> bool);
    }

    /// When two orswots have identical clocks, but different elements,
    /// any non-common elements will be dropped.  This highlights the
    /// proper usage of orswots: don't use the same witness from different
    /// copies of the orswot, or elements will be deleted upon merge.
    #[test]
    fn weird_highlight_1() {
        let (mut a, mut b) = (Orswot::<u8, u8>::new(), Orswot::<u8, u8>::new());
        let a_read_ctx = a.value();
        let b_read_ctx = b.value();
        let op_a = a.add(1, a_read_ctx.derive_add_ctx(1));
        let op_b = b.add(2, b_read_ctx.derive_add_ctx(1));
        a.apply(&op_a);
        b.apply(&op_b);
        a.merge(&b);
        assert!(a.value().val.is_empty());
    }

    /// 
    #[test]
    fn adds_dont_destroy_causality() {
        let (mut a, mut b) = (Orswot::<String, String>::new(), Orswot::<String, String>::new());
        let ctx = vec![("actor 1".to_string(), 2), ("actor 2".to_string(), 2)]
            .into_iter()
            .collect();
        let a_read_ctx = a.value();
        let a_op1 = a.add("element", a_read_ctx.derive_add_ctx("actor 7".to_string()));
        a.apply(&a_op1);
        b.apply_remove("element", &ctx);
        
        let a_op2 = a.add("element", a.value().derive_add_ctx("actor 1".to_string()));
        a.apply(&a_op2);

        a.merge(&b);
        assert_eq!(a.value().val, vec!["element".to_string()]);
    }

    #[test]
    // a bug found with rust quickcheck where deferred operations
    // are not carried over after a merge.
    // symptoms:
    //  if nothing is added, it works
    //  if removed elem is added first, it only misses one
    //  if non-related elem is added, it misses both
    fn ensure_deferred_merges() {
        let (mut a, mut b) = (Orswot::<String, u8>::new(), Orswot::<String, u8>::new());

        let b_read_ctx = b.value();
        let b_op1 = b.add("element 1", b_read_ctx.derive_add_ctx(5));
        b.apply(&b_op1);

        // remove with a future context
        b.apply_remove("element 1", &Dot { actor: 5, counter: 4 }.into());
        
        let a_read_ctx = a.value();
        let a_op = a.add("element 4", a_read_ctx.derive_add_ctx(6));
        a.apply(&a_op);
        
        // remove with a future context
        b.apply_remove("element 9", &Dot { actor: 4, counter: 4 }.into());

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
        let (mut a, mut b, mut c) =
            (Orswot::<u8, u8>::new(), Orswot::<u8, u8>::new(), Orswot::<u8, u8>::new());
        // add element 5 from witness 1
        let op = a.add(5, a.value().derive_add_ctx(1));
        a.apply(&op);

        // on another clock, remove 5 with an advanced clock for witnesses 1 and 4
        let mut vc = VClock::new();
        vc.witness(1, 3).unwrap();
        vc.witness(4, 8).unwrap();

        // remove from b (has not yet seen add for 5) with advanced ctx
        b.apply_remove(5, &vc);
        assert_eq!(b.deferred.len(), 1);

        // ensure that the deferred elements survive across a merge
        c.merge(&b);
        assert_eq!(c.deferred.len(), 1);

        // after merging the set with deferred elements with the set that contains
        // an inferior member, ensure that the member is no longer visible and
        // the deferred set still contains this info
        a.merge(&c);
        assert!(a.value().val.is_empty());
    }

    // a bug found with rust quickcheck where identical entries
    // with different associated clocks were removed rather
    // than merged.
    #[test]
    fn merge_clocks_of_identical_entries() {
        let (mut a, mut b) = (Orswot::<u8, u8>::new(), Orswot::<u8, u8>::new());
        // add element 1 with witnesses 3 and 7
        let a_op = a.add(1, a.value().derive_add_ctx(3));
        a.apply(&a_op);
        let b_op = a.add(1, b.value().derive_add_ctx(7));
        b.apply(&b_op);
        a.merge(&b);
        assert_eq!(a.value().val, vec![1]);
        let mut expected_clock = VClock::new();
        let op_3 = expected_clock.inc(3);
        let op_7 = expected_clock.inc(7);
        expected_clock.apply(&op_3);
        expected_clock.apply(&op_7);
        assert_eq!(a.entries.get(&1), Some(&expected_clock));
    }

    // port from riak_dt
    #[test]
    fn test_disjoint_merge() {
        let (mut a, mut b) = (Orswot::<String, String>::new(), Orswot::<String, String>::new());
        let a_op = a.add("bar", a.value().derive_add_ctx("A".to_string()));
        a.apply(&a_op);
        assert_eq!(a.value().val, vec!["bar".to_string()]);
        let b_op = b.add("baz", b.value().derive_add_ctx("B".to_string()));
        b.apply(&b_op);
        assert_eq!(b.value().val, vec!["baz".to_string()]);
        let mut c = a.clone();
        assert_eq!(c.value().val, vec!["bar".to_string()]);
        c.merge(&b);
        assert_eq!(c.value().val, vec!["bar".to_string(), "baz".to_string()]);

        let rm_ctx = a.entries.get(&"bar".to_string()).unwrap().clone();
        a.apply_remove("bar", &rm_ctx);
        let mut d = a.clone();
        d.merge(&c);
        assert_eq!(d.value().val, vec!["baz".to_string()]);
    }

    // port from riak_dt
    // Bug found by EQC, not dropping dots in merge when an element is
    // present in both Sets leads to removed items remaining after merge.
    #[test]
    fn test_present_but_removed() {
        let (mut a, mut b) = (Orswot::<String, String>::new(), Orswot::<String, String>::new());
        let a_op = a.add("Z", a.value().derive_add_ctx("A".to_string()));
        a.apply(&a_op);
        // Replicate it to C so A has 'Z'->{e, 1}
        let c = a.clone();
        
        let a_rm_ctx = a.entries.get(&"Z".to_string()).unwrap().clone();
        a.apply_remove("Z", &a_rm_ctx);
        assert_eq!(a.deferred.len(), 0);

        let b_op = b.add("Z", b.value().derive_add_ctx("B".to_string()));
        b.apply(&b_op);

        // Replicate B to A, so now A has a Z, the one with a Dot of
        // {b,1} and clock of [{a, 1}, {b, 1}]
        a.merge(&b);
        let b_rm_ctx = b.entries.get(&"Z".to_string()).unwrap().clone();
        b.apply_remove("Z", &b_rm_ctx);
        // Both C and A have a 'Z', but when they merge, there should be
        // no 'Z' as C's has been removed by A and A's has been removed by
        // C.
        a.merge(&b);
        a.merge(&c);
        assert!(a.value().val.is_empty());
    }

    // port from riak_dt
    // A bug EQC found where dropping the dots in merge was not enough if
    // you then store the value with an empty clock (derp).
    #[test]
    fn test_no_dots_left_test() {
        let (mut a, mut b) = (Orswot::<String, u8>::new(), Orswot::<String, u8>::new());
        let a_op = a.add("Z", a.value().derive_add_ctx(1));
        a.apply(&a_op);
        let b_op = b.add("Z", b.value().derive_add_ctx(2));
        b.apply(&b_op);
        let c = a.clone();
        let a_rm_ctx = a.entries.get(&"Z".to_string()).unwrap().clone();
        a.apply_remove("Z", &a_rm_ctx);

        // replicate B to A, now A has B's 'Z'
        a.merge(&b);
        assert_eq!(a.value().val, vec!["Z".to_string()]);

        let mut expected_clock = VClock::new();
        let op_1 = expected_clock.inc(1);
        let op_2 = expected_clock.inc(2);
        expected_clock.apply(&op_1);
        expected_clock.apply(&op_2);

        assert_eq!(a.clock, expected_clock);

        let b_rm_ctx = b.entries.get(&"Z".to_string()).unwrap().clone();
        b.apply_remove("Z", &b_rm_ctx);
        assert!(b.value().val.is_empty());

        // Replicate C to B, now B has A's old 'Z'
        b.merge(&c);
        assert_eq!(b.value().val, vec!["Z".to_string()]);

        // Merge everything, without the fix You end up with 'Z' present,
        // with no dots
        b.merge(&a);
        b.merge(&c);

        assert!(b.value().val.is_empty());
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
        let mut a = Orswot::<String, u8>::new();
        let a_op = a.add("A", a.value().derive_add_ctx(1));
        assert_eq!(a_op, super::Op::Add { dot: Dot { actor: 1, counter: 1 }, member: "A".into() });
        a.apply(&a_op);
        assert_eq!(a.entries.get(&"A".to_string()).unwrap(), &VClock::from(Dot { actor: 1u8, counter: 1 }));

        let mut b = a.clone();
        let b_op = b.add("B", b.value().derive_add_ctx(2));
        b.apply(&b_op);
        let bctx = b.value().add_clock;
        assert_eq!(bctx, vec![(1, 1), (2, 1)].into());
        a.apply_remove("A", &bctx);
        assert_eq!(a.value().val, Vec::<String>::new());
    }

    #[test]
    fn test_reset_remove_semantics() {
        use map::Map;
        let mut m1: Map<u8, Orswot<u8, u8>, u8> = Map::new();

        let op1 = m1.update(
            101,
            m1.get(&101).derive_add_ctx(75),
            |set, ctx| set.add(1, ctx.clone())
        );
        m1.apply(&op1);

        let mut m2 = m1.clone();

        let read_ctx = m1.get(&101);
        let op2 = m1.rm(101, read_ctx.derive_rm_ctx());
        m1.apply(&op2);
        let op3 = m2.update(
            101,
            m2.get(&101).derive_add_ctx(93),
            |set, ctx| set.add(2, ctx.clone())
        );
        m2.apply(&op3);

        assert_eq!(m1.get(&101).val, None);
        assert_eq!(m2.get(&101).val.unwrap().value().val, vec![1, 2]);

        let snapshot = m1.clone();
        m1.merge(&m2);
        m2.merge(&snapshot);

        assert_eq!(m1, m2);
        assert_eq!(m1.get(&101).val.unwrap().value().val, vec![2]);
    }
}
