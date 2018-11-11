use std::cmp::Ordering;
use std::fmt::{self, Debug, Display};

use vclock::{VClock, Actor};
use ctx::{ReadCtx, AddCtx};
use traits::{Causal, CmRDT, CvRDT};

/// A Trait alias for the possible values MVReg's may hold
pub trait Val: Debug + Clone {}
impl<T: Debug + Clone> Val for T {}

/// MVReg (Multi-Value Register)
/// On concurrent writes, we will keep all values for which
/// we can't establish a causal history.
///
/// ```rust
/// use crdts::{CmRDT, MVReg, Dot, VClock};
/// let mut r1 = MVReg::<String, u8>::new();
/// let mut r2 = r1.clone();
/// let r1_read_ctx = r1.read();
/// let r2_read_ctx = r2.read();
///
/// let op1 = r1.write("bob", r1_read_ctx.derive_add_ctx(123));
/// r1.apply(&op1);
///
/// let op2 = r2.write("alice", r2_read_ctx.derive_add_ctx(111));
/// r2.apply(&op2);
///
/// r1.apply(&op2); // we replicate op2 to r1
/// 
/// let read_ctx = r1.read();
/// assert_eq!(read_ctx.val, vec!["bob".to_string(), "alice".to_string()]);
/// assert_eq!(
///     read_ctx.add_clock,
///     vec![Dot::new(123, 1), Dot::new(111, 1)]
///       .into_iter()
///       .collect()
/// );
/// ```
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MVReg<V: Val, A: Actor> {
    vals: Vec<(VClock<A>, V)>
}

/// Defines the set of operations over the MVReg
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Op<V: Val, A: Actor> {
    /// Put a value
    Put {
        /// context of the operation
        clock: VClock<A>,
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
            write!(f, "{}@{}", val, ctx)?;
        }
        write!(f, "|")
    }
}

impl<V: Val + PartialEq, A: Actor> PartialEq for MVReg<V, A> {
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

impl<V: Val + Eq, A: Actor> Eq for MVReg<V, A> {}

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
        MVReg::new()
    }
}

impl<V: Val, A: Actor> CvRDT for MVReg<V, A> {
    fn merge(&mut self, other: &Self) {
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
                for (existing_c, _) in vals.iter() {
                    if existing_c == clock {
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
    }
}

impl<V: Val, A: Actor> CmRDT for MVReg<V, A> {
    type Op = Op<V, A>;

    fn apply(&mut self, op: &Self::Op) {
        match op.clone() {
            Op::Put { clock, val } => {
                if clock.is_empty() {
                    return;
                }
                // first filter out all values that are dominated by the Op clock
                self.vals.retain(|(val_clock, _)| match val_clock.partial_cmp(&clock) {
                    None | Some(Ordering::Greater) => true,
                    _ => false
                });

                // TAI: in the case were the Op has a context that already was present,
                //      the above line would remove that value, the next lines would
                //      keep the val from the Op, so.. a malformed Op could break
                //      comutativity.
                
                // now check if we've already seen this op
                let mut should_add = true;
                for (existing_clock, _) in self.vals.iter() {
                    if existing_clock > &clock {
                        // we've found an entry that dominates this op
                        should_add = false;
                    }
                }

                if should_add {
                    self.vals.push((clock, val));
                }
            }
        }
    }
}

impl<V: Val, A: Actor> MVReg<V, A> {
    /// Construct a new empty MVReg
    pub fn new() -> Self {
        MVReg { vals: Vec::new() }
    }

    /// Set the value of the register
    pub fn write(&self, val: impl Into<V>, ctx: AddCtx<A>) -> Op<V, A> {
        Op::Put { clock: ctx.clock, val: val.into() }
    }

    /// Consumes the register and returns the values
    pub fn read(&self) -> ReadCtx<Vec<V>, A> {
        let clock = self.clock().clone();
        let concurrent_vals = self.vals
            .iter()
            .cloned()
            .map(|(_, v)| v)
            .collect();
        ReadCtx {
            add_clock: clock.clone(),
            rm_clock: clock,
            val: concurrent_vals
        }
    }

    /// A clock with latest versions of all actors operating on this register
    fn clock(&self) -> VClock<A> {
        self.vals.iter()
            .fold(VClock::new(), |mut accum_clock, (c, _)| {
                accum_clock.merge(&c);
                accum_clock
            })
    }
}
