use serde::de::DeserializeOwned;
use serde::Serialize;

use std::fmt::{self, Debug, Display};

use error::{Error, Result};
use vclock::{VClock, Dot, Actor};
use traits::{Causal, CmRDT, CvRDT};

/// A Trait alias for the possible values MVReg's may hold
pub trait Val: Debug + Eq + Clone + Send + Serialize + DeserializeOwned {}
impl<T: Debug + Eq + Clone + Send + Serialize + DeserializeOwned> Val for T {}

/// MVReg expands to Multi-Value Register.
/// On merge, we will keep all values for which we can't establish a causal history.
///
/// ```rust
/// use crdts::{CvRDT, MVReg, Dot};
/// let (r1, r2) = (MVReg::<String, u8>::new(), MVReg::<String, u8>::new());
/// let op1 = r1.set("bob", Dot { actor: 123, counter: 6 });
/// r1.apply(&op1);
/// let op2 = r2.set("alice", Dot { actor: 111, counter: 3 });
/// r2.apply(&op2);
///
/// r1.apply(&op2);
/// assert_eq!(r1.get_owned(), (vec!["alice", "bob"], vec![(123, 6), (111, 3)].into_iter().collect()));
/// ```
#[serde(bound(deserialize = ""))]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MVReg<V: Val, A: Actor> {
    vals: Vec<(VClock<A>, V)>
}

/// Defines the set of operations over the MVReg
#[serde(bound(deserialize = ""))]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Op<V: Val, A: Actor> {
    /// Put a value under some context
    Put {
        /// context of the operation
        ctx: VClock<A>,
        /// the value to put
        val: V
    }
}

impl<V: Val + Display, A: Actor + Display> Display for MVReg<V, A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "|")?;
        for (i, (ctx, val)) in self.vals.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{{{}}}@{}", val, ctx)?;
        }
        write!(f, "|")
    }
}

impl<V: Val, A: Actor> PartialEq for MVReg<V, A> {
    fn eq(&self, other: &Self) -> bool {
        for dot in self.vals.iter() {
            let mut num_found = other.vals.iter().filter(|d| d == &dot).count();

            if num_found == 0 {
                return false
            }
            // sanity check
            assert_eq!(num_found, 1);
        }
        for dot in other.vals.iter() {
            let mut num_found = self.vals.iter().filter(|d| d == &dot).count();

            if num_found == 0 {
                return false
            }
            // sanity check
            assert_eq!(num_found, 1);
        }
        true
    }
}

impl<V: Val, A: Actor> Eq for MVReg<V, A> {}

impl<V: Val, A: Actor> Causal<A> for MVReg<V, A> {
    fn truncate(&mut self, clock: &VClock<A>) {
        self.vals = self.vals.clone().into_iter()
            .filter_map(|(mut val_clock, val)| {
                val_clock.subtract(&clock);
                if val_clock.is_empty() {
                    None
                } else {
                    Some((val_clock, val))
                }
            })
            .collect()
    }
}

impl<V: Val, A: Actor> Default for MVReg<V, A> {
    fn default() -> Self {
        MVReg { vals: Vec::new() }
    }
}

impl<V: Val, A: Actor> CvRDT for MVReg<V, A> {
    type Error = Error;

    fn merge(&mut self, other: &Self) -> Result<()> {
        let mut vals = Vec::new();
        for (clock, val) in self.vals.iter() {
            let num_dominating = other.vals
                .iter()
                .filter(|(c, _)| clock < c)
                .count();
            if num_dominating == 0 {
                vals.push((clock.clone(), val.clone()));
            }
        }
        for (clock, val) in other.vals.iter() {
            let num_dominating = self.vals
                .iter()
                .filter(|(c, _)| clock < c)
                .count();
            if num_dominating == 0 {
                let mut is_new = true;
                for (existing_c, existing_v) in vals.iter() {
                    if existing_c == clock {
                        // sanity check
                        assert_eq!(val, existing_v);
                        is_new = false;
                        break;
                    }
                }
                if is_new {
                    vals.push((clock.clone(), val.clone()));
                }
            }
        }
        self.vals = vals;
        Ok(())
    }
}

impl<V: Val, A: Actor> CmRDT for MVReg<V, A> {
    type Op = Op<V, A>;
    type Error = Error;

    fn apply(&mut self, op: &Self::Op) -> Result<()> {
        match op.clone() {
            Op::Put { ctx, val } => {
                if ctx.is_empty() {
                    return Ok(());
                }
                // first filter out all values that are dominated by the Op ctx
                self.vals.retain(|(val_ctx, _)| !(val_ctx < &ctx));

                // now check if we've already seen this op
                let mut should_add = true;
                for (existing_ctx, existing_val) in self.vals.iter() {
                    if existing_ctx == &ctx && existing_val != &val {
                        return Err(Error::ConflictingDot);
                    } else if existing_ctx >= &ctx {
                        // we've found an entry that descends this op
                        should_add = false;
                        // don't break out of this loop!
                        // we need to finish our conflicting dot check
                    }
                }
                if should_add {
                    self.vals.push((ctx, val));
                }
            }
        }
        Ok(())
    }
}

impl<V: Val, A: Actor> MVReg<V, A> {
    /// Construct a new empty MVReg
    pub fn new() -> Self {
        MVReg::default()
    }

    /// Set the value with a dot
    pub fn set(&self, val: impl Into<V>, dot: &Dot<A>) -> Op<V, A> {
        let mut ctx = self.context();
        ctx.apply(&dot).unwrap();
        Op::Put { ctx, val: val.into() }
    }

    /// Returns all values stored in the register with their causal context
    pub fn get_owned(self) -> (Vec<V>, VClock<A>) {
        let ctx = self.context();
        let concurrent_vals = self.vals.into_iter().map(|(_, v)| v).collect();
        (concurrent_vals, ctx)
    }

    /// Returns a ref to values stored in the register with their causal context
    pub fn get(&self) -> (Vec<&V>, VClock<A>) {
        let ctx = self.context();
        let concurrent_vals = self.vals.iter().map(|(_, v)| v).collect();
        (concurrent_vals, ctx)
    }

    /// Returns th causal context for the register
    pub fn context(&self) -> VClock<A> {
        self.vals.iter()
            .fold(VClock::new(), |mut accum_clock, (c, _)| {
                accum_clock.merge(&c);
                accum_clock
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::fmt;
    use quickcheck::{Arbitrary, Gen, TestResult};

    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
    struct TActor(u8);
    
    #[derive(Debug, Clone)]
    struct TestReg<V: Val, A: Actor> {
        reg: MVReg<V, A>,
        ops: Vec<Op<V, A>>
    }

    impl<V: Val, A: Actor> TestReg<V, A> {
        fn incompat(&self, other: &Self) -> bool {
            for (c1, v1) in self.reg.vals.iter() {
                for (c2, v2) in other.reg.vals.iter() {
                    if c1 == c2 && v1 != v2 {
                        return true;
                    }
                }
            }

            for Op::Put { ctx: c, val: v } in self.ops.iter() {
                for Op::Put { ctx: other_c, val: other_v } in other.ops.iter() {
                    if c == other_c && v != other_v {
                        return true;
                    }
                }
            }

            return false;
        }
    }

    impl Arbitrary for TActor {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            let actor: u8 = g.gen_range(0, 10);
            TActor(actor)
        }
        fn shrink(&self) -> Box<Iterator<Item = Self>> {
            Box::new(vec![].into_iter())
        }
    }

    impl Debug for TActor {
        fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            write!(formatter, "A{}", self.0)
        }
    }
    
    impl<V: Val + Arbitrary, A: Actor + Arbitrary>  Arbitrary for TestReg<V, A> {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            let mut reg: MVReg<V, A> = MVReg::default();
            let num_ops = g.gen::<u8>() % 20;
            let mut ops = Vec::with_capacity(num_ops as usize);
            for _ in 0..num_ops {
                let val = V::arbitrary(g);
                let actor = A::arbitrary(g);
                let dot = reg.context().inc(actor);
                let op = reg.set(val, &dot);
                reg.apply(&op).unwrap();
                ops.push(op);
            }
            TestReg { reg, ops }
        }

        fn shrink(&self) -> Box<Iterator<Item = Self>> {
            let mut shrunk = vec![];

            for i in (0..self.ops.len()).into_iter().rev() {
                let mut reg = MVReg::new();
                let mut ops = Vec::with_capacity(self.ops.len() - 1);
                
                for (j, op) in self.ops.iter().cloned().enumerate() {
                    if i == j {
                        continue;
                    }

                    reg.apply(&op).unwrap();
                    ops.push(op);
                }

                shrunk.push(TestReg { reg, ops });

                let Op::Put { ctx, val } = self.ops[i].clone();
                for dot in ctx.clone().into_iter() {
                    let shrunk_ctx: VClock<A> = ctx.clone()
                        .into_iter()
                        .filter(|d| d != &dot)
                        .collect();

                    if shrunk_ctx.is_empty() {
                        continue;
                    }
                    
                    let mut reg = MVReg::new();
                    let mut ops = self.ops.clone();
                    ops[i] = Op::Put {
                        ctx: shrunk_ctx,
                        val: val.clone()
                    };
                    let mut conflict = false;
                    for op in ops.iter() {
                        conflict = reg.apply(&op).is_err();
                        if conflict { break; }
                    }
                    if !conflict {
                        shrunk.push(TestReg { reg, ops });
                    }
                }
            }
            Box::new(shrunk.into_iter())
        }
    }

    #[test]
    fn test_apply() {
        let mut reg = MVReg::new();
        let ctx = VClock::from(Dot { actor: 2, counter: 1 });
        reg.apply(&Op::Put { ctx: ctx.clone(), val: 71 }).unwrap();
        assert_eq!(reg, MVReg { vals: vec![(ctx, 71)] });
    }

    #[test]
    fn test_set_should_not_mutate_reg() {
        let reg = MVReg::<u8, u8>::new();
        let op = reg.set(32, &Dot { actor: 1, counter: 2 });
        assert_eq!(reg, MVReg::new());
        let mut reg = reg;
        reg.apply(&op).unwrap();

        let (vals, ctx) = reg.get();
        assert_eq!(vals, vec![&32]);
        assert_eq!(ctx, VClock::from(Dot { actor: 1, counter: 2 }));
    }

    #[test]
    fn test_concurrent_update_with_same_value_dont_collapse_on_merge() {
        // this is important to prevent because it breaks commutativity
        let mut r1 = MVReg::new();
        let mut r2 = MVReg::new();

        let op1 = r1.set(23, &Dot { actor: 4, counter: 1 });
        let op2 = r2.set(23, &Dot { actor: 7, counter: 1 });
        r1.apply(&op1).unwrap();
        r2.apply(&op2).unwrap();

        r1.merge(&r2).unwrap();
        assert_eq!(r1.get(), (vec![&23, &23], VClock::from(vec![(4, 1), (7, 1)])));
    }

    #[test]
    fn test_concurrent_update_with_same_value_collapse_on_apply() {
        // this is important to prevent because it breaks commutativity
        let mut r1 = MVReg::new();
        let r2 = MVReg::new();

        let op1 = r1.set(23, &Dot { actor: 4, counter: 1 });
        r1.apply(&op1).unwrap();
        let op2 = r2.set(23, &Dot { actor: 7, counter: 1 });

        r1.apply(&op2).unwrap();
        assert_eq!(r1.get(), (vec![&23, &23], VClock::from(vec![(4, 1), (7, 1)])));
    }

    #[test]
    fn test_multi_get() {
        let mut r1 = MVReg::<u8, u8>::new();
        let mut r2 = MVReg::<u8, u8>::new();
        let op1 = r1.set(32, &Dot { actor: 1, counter: 1 });
        let op2 = r2.set(82, &Dot { actor: 2, counter: 1 });
        r1.apply(&op1).unwrap();
        r2.apply(&op2).unwrap();

        r1.merge(&r2).unwrap();
        let (vals, _) = r1.get();
        assert!(vals == vec![&32, &82] || vals == vec![&82, &32]);
    }

    #[test]
    fn test_op_commute_quickcheck1() {
        let mut reg1 = MVReg::new();
        let mut reg2 = MVReg::new();

        let op1 = Op::Put { ctx: Dot { actor: 1, counter: 1 }.into(), val: 1 };
        let op2 = Op::Put { ctx: Dot { actor: 2, counter: 1 }.into(), val: 2 };

        reg2.apply(&op2).unwrap();
        reg2.apply(&op1).unwrap();
        reg1.apply(&op1).unwrap();
        reg1.apply(&op2).unwrap();

        assert_eq!(reg1, reg2);
    }

    quickcheck! {
        fn prop_sanity_check_arbitrary(r: TestReg<u8, TActor>) -> bool {
            let mut reg = MVReg::new();
            for op in r.ops.iter() {
                reg.apply(op).unwrap();
            }

            assert_eq!(reg, r.reg);
            true
        }

        fn prop_set_with_dot_from_get_ctx(r: TestReg<u8, TActor>, a: TActor) -> bool {
            let mut reg = r.reg;
            let (_, ctx) = reg.get();
            let counter = ctx.get(&a) + 1;
            let dot = Dot {
                actor: a,
                counter
            };
            let op = reg.set(23, &dot);
            reg.apply(&op).unwrap();

            let (vals, _) = reg.get();
            vals == vec![&23]
        }
        
        fn prop_merge_idempotent(r: TestReg<u8, TActor>) -> bool {
            let mut r = r.reg;
            let r_snapshot = r.clone();

            assert!(r.merge(&r_snapshot).is_ok());

            assert_eq!(r, r_snapshot);
            true
        }

        fn prop_merge_commutative(r1: TestReg<u8, TActor>, r2: TestReg<u8, TActor>) -> TestResult {
            if r1.incompat(&r2) {
                return TestResult::discard();
            }
            let mut r1 = r1.reg;
            let mut r2 = r2.reg;

            let r1_snapshot = r1.clone();
            assert!(r1.merge(&r2).is_ok());
            assert!(r2.merge(&r1_snapshot).is_ok());

            assert_eq!(r1, r2);
            TestResult::from_bool(true)
        }

        fn prop_merge_associative(r1: TestReg<u8, TActor>, r2: TestReg<u8, TActor>, r3: TestReg<u8, TActor>) -> TestResult {
            if r1.incompat(&r2) || r1.incompat(&r3) || r2.incompat(&r3) {
                return TestResult::discard();
            }
            let mut r1 = r1.reg;
            let mut r2 = r2.reg;
            let r3 = r3.reg;
            let r1_snapshot = r1.clone();
            
            // r1 ^ r2
            assert!(r1.merge(&r2).is_ok());

            // (r1 ^ r2) ^ r3
            assert!(r1.merge(&r3).is_ok());

            // r2 ^ r3
            assert!(r2.merge(&r3).is_ok());

            // r1 ^ (r2 ^ r3)
            assert!(r2.merge(&r1_snapshot).is_ok());

            assert_eq!(r1, r2);
            TestResult::from_bool(true)
        }

        fn prop_truncate(r: TestReg<u8, TActor>) -> bool{
            let mut r = r.reg;
            let r_snapshot = r.clone();

            // truncating with the empty clock should be a nop
            r.truncate(&VClock::new());
            assert_eq!(r, r_snapshot);

            // truncating with the merge of all val clocks should give us
            // an empty register
            let clock = r.vals
                .iter()
                .fold(VClock::new(), |mut accum_clock, (c, _)| {
                    accum_clock.merge(&c);
                    accum_clock
                });

            r.truncate(&clock);
            assert_eq!(r, MVReg::new());
            true
        }

        fn prop_op_idempotent(test: TestReg<u8, TActor>) -> TestResult {
            let mut r = test.reg;
            let r_snapshot = r.clone();
            for op in test.ops.iter() {
                assert!(r.apply(op).is_ok());
            }

            assert_eq!(r, r_snapshot);
            TestResult::from_bool(true)
        }

        fn prop_op_commutative(o1: TestReg<u8, TActor>, o2: TestReg<u8, TActor>) -> TestResult {
            if o1.incompat(&o2) {
                return TestResult::discard();
            }

            let mut r1 = o1.reg;
            let mut r2 = o2.reg;

            for op in o2.ops.iter() {
                r1.apply(op).unwrap();
            }
            
            for op in o1.ops.iter() {
                r2.apply(op).unwrap();
            }

            assert_eq!(r1, r2);
            TestResult::from_bool(true)
        }

        fn prop_op_associative(o1: TestReg<u8, TActor>, o2: TestReg<u8, TActor>, o3: TestReg<u8, TActor>) -> TestResult {
            if o1.incompat(&o2) || o1.incompat(&o3) || o2.incompat(&o3) {
                return TestResult::discard();
            }

            let mut r1 = o1.reg;
            let mut r2 = o2.reg;


            // r1 <- r2
            for op in o2.ops.iter() {
                r1.apply(op).unwrap();
            }

            // (r1 <- r2) <- r3
            for op in o3.ops.iter() {
                r1.apply(op).unwrap();
            }

            // r2 <- r3
            for op in o3.ops.iter() {
                r2.apply(op).unwrap();
            }

            // (r2 <- r3) <- r1
            for op in o1.ops.iter() {
                r2.apply(op).unwrap();
            }

            assert_eq!(r1, r2);
            TestResult::from_bool(true)
        }
    }
}
