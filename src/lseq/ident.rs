use rand::Rng;
use serde::{Deserialize, Serialize};
use bitvec::vec::*;

const BOUNDARY: u64 = 10;

const INITIAL_BASE: u32 = 3; // start with 2^8

/// A tree identifier uniquely locates a character in an LSeq tree
/// it represents the path that needs to be taken in order to reach
/// the character. At each level we store the index of the child tree node
/// as well as the id of the site that inserted that node. This resolves conflicts where
/// two sites decide to pick the same child index to allocate a fresh node
#[derive(Debug, PartialEq, PartialOrd, Ord, Eq, Clone, Serialize, Deserialize, Hash)]
pub struct Identifier {
    path: Vec<(u64, u32)>,
    // site_id: u64,
    // counter: u64
}
impl Identifier {
    /// Get the size of an identifier
    pub fn len(&self) -> usize {
        self.path.len()
    }
}
/// Generates fresh identifiers
///
/// These identifiers represent a path in an exponential tree. At each level of the tree the amount
/// of children doubles. This means that we can store a lot of nodes in a very low height!
///
/// The LSeq tree also has an additional restriction: at each level the minimum and maximum nodes
/// cannot be chosen when allocating fresh nodes. This is to ensure there is always a free node
/// that can be used to create a lower level.
//#[derive(Serialize, Deserialize)]
pub struct IdentGen {
    initial_base_bits: u32,
    strategy_vec: BitVec,
    /// Site id of this tree
    pub site_id: u32,
    // clock: u64
}

impl IdentGen {
    /// Create a fresh tree with 0 node
    pub fn new(site_id: u32) -> IdentGen {
        Self::new_with_args(INITIAL_BASE, site_id)
    }

    /// Create a tree with a custom initial size
    pub fn new_with_args(base: u32, site_id: u32) -> IdentGen {
        IdentGen { initial_base_bits: base, strategy_vec: BitVec::new(), site_id }
    }

    /// The smallest possible node in a tree
    pub fn lower(&self) -> Identifier {
        Identifier { path: vec![(0, 0)] }
    }

    /// The absolute largest possible node
    pub fn upper(&self) -> Identifier {
        Identifier { path: vec![(2u64.pow(self.initial_base_bits) - 1, 0)] }
    }
    /// Allocates a new identifier between p and q.
    /// Requires that p < q and will produce a new identifier z, p < z < q
    ///
    /// The way to think about this is to consider the problem of finding a short number between
    /// two decimal numbers. For example, between 0.2 and 0.4 we'd like to return 0.3
    /// But what about 0.2 and 0.3? Well a nice property is that if we add a digit to 0.2, the
    /// number produced will be larger than 0.2 but smaller than 0.3.
    ///
    /// If you view identifiers p and q as decimal numbers 0.p and 0.q. Then all we're doing is
    /// finding a number between them!
    ///
    ///
    pub fn alloc(&mut self, p: &Identifier, q: &Identifier) -> Identifier {
        assert!(p < q, "lower bound should be smaller than upper bound!");
        let mut depth = 0;

        // Descend both identifiers in parallel until we find room to insert an identifier
        loop {
            match (p.path.get(depth), q.path.get(depth)) {
                // Our descent continues...
                (Some(a), Some(b)) => {
                    if a.0 == b.0 {
                        // continue searching lower
                    } else if a.0 + 1 < b.0 {
                        // We take this branch if there's room between a and b to insert a new
                        // identifier
                        let next_index = self.index_in_range(a.0 + 1, b.0, depth as u32);
                        return self.replace_last(p, depth, next_index);
                    } else {
                        // If we end up here that means that a + 1 = b. Therefore we can't actually
                        // insert a new node at this layer. So we start a new layer below a.
                        return self.alloc_from_lower(p, depth + 1);
                    }
                }

                // The upper bound ended on the previous level.
                // This means we can allocate a node in the range a..max_for_depth
                // If there isn't room at this level because a = max_for_depth then we'll keep
                // searching below.
                (Some(_), None) => {
                    return self.alloc_from_lower(p, depth);
                }
                // The lower bound ended on the previous level, we just need to keep following the upper bound until some space
                // is available.
                (None, Some(_)) => {
                    return self.alloc_from_upper(p, q, depth);
                }

                // The two paths are fully equal which means that the site_ids MUST be different or
                // we are in an invalid situation
                (None, None) => {
                    let max_for_depth = self.width_at(depth) - 1;
                    let next_index = self.index_in_range(1, max_for_depth, depth as u32);
                    return self.push_index(p, next_index);
                }
            };
            depth += 1;
        }
    }

    // Here we have the lowest possible upper bound and we just need to traverse the lower bound
    // until we can find somehwere to insert a new identifier.
    //
    // This reflects the case where we want to allocate between 0.20001 and 0.3
    fn alloc_from_lower(&mut self, p: &Identifier, mut depth: usize) -> Identifier {
        loop {
            match p.path.get(depth) {
                Some((ix, _)) => {
                    if ix + 1 < self.width_at(depth) {
                        let next_index = self.index_in_range(ix + 1, self.width_at(depth), depth as u32);
                        return self.replace_last(p, depth, next_index);
                    }
                }
                None => {
                    let next_index = self.index_in_range(1, self.width_at(depth), depth as u32);
                    return self.push_index(p, next_index);
                }
            }
            depth += 1;
        }
    }

    // Here the problem is that we've run out of the lower path and the upper one is zero!
    // The idea is to keep pushing 0s onto the lower path until we can find a new level to allocate at.
    //
    // This reflects the case where we want to allocate something between 0.2 and 0.200000001
    fn alloc_from_upper(&mut self, base: &Identifier, q: &Identifier, mut depth: usize) -> Identifier {
        let mut ident = base.clone();
        loop {
            match q.path.get(depth) {
                // append a 0 to the result path as well
                Some(b) if b.0 <= 1 => ident.path.push((0, b.1)),
                // oo! a non-zero value
                _ => break,
            }
            depth += 1;
        }

        // If we actually ran out of upper bound values then we're free to choose
        // anything on the next level, otherwise use the upper bound we've found.
        let upper = match q.path.get(depth) {
            Some(b) => b.0,
            None => self.width_at(depth + 1),
        };
        let next_index = self.index_in_range(1, upper, depth as u32);
        return self.push_index(&ident, next_index);
    }

    fn replace_last(&mut self, p: &Identifier, depth: usize, ix: u64) -> Identifier {
        let mut ident = p.clone();
        ident.path.truncate(depth);
        ident.path.push((ix, self.site_id));
        ident
    }

    fn push_index(&mut self, p: &Identifier, ix: u64) -> Identifier {
        let mut ident = p.clone();
        ident.path.push((ix, self.site_id));
        ident
    }

    fn width_at(&self, depth: usize) -> u64 {
        2u64.pow(self.initial_base_bits + depth as u32)
    }
    // Generate an index in a given range at the specified depth.
    // Uses the allocation strategy of that depth, boundary+ or boundary- which is biased to the
    // lower and upper ends of the range respectively.
    // should allocate in the range [lower, upper)
    fn index_in_range(&mut self, lower: u64, upper: u64, depth: u32) -> u64 {
        assert!(lower < upper, "need at least one space between the bounds lower={} upper={}", lower, upper);

        let mut rng = rand::rngs::OsRng;
        let interval = BOUNDARY.min(upper - 1 - lower);
        let step = if interval > 0 { rng.gen_range(0, interval) } else { 0 };
        if self.strategy(depth) {
            //boundary+
            lower + step
        } else {
            //boundary-
            upper - step - 1
        }
    }

    fn strategy(&mut self, depth: u32) -> bool {
        match self.strategy_vec.get(depth as usize) {
            None => {
                self.strategy_vec.push(rand::thread_rng().gen());
                self.strategy(depth)

            }
            Some(s) => *s
        }
        // temp strategy. Should be a random choice at each level
    }
}

#[cfg(test)]
impl quickcheck::Arbitrary for Identifier {
    fn arbitrary<G: quickcheck::Gen>(g: &mut G) -> Identifier {
        Identifier { path: Vec::<(u64, u32)>::arbitrary(g) }
    }
}


#[cfg(test)]
mod test {
    use super::*;
    use quickcheck::{quickcheck, Arbitrary, Gen, TestResult};

    quickcheck! {
        fn prop_alloc(p: Identifier, q: Identifier) -> TestResult {
            if p >= q || p.len() == 0 || q.len() == 0 {
                return TestResult::discard();
            }
            let mut gen = IdentGen::new(0);
            let z = gen.alloc(&p, &q);

            TestResult::from_bool(p < z && z < q)
        }
    }

    #[test]
    fn test_alloc_eq_path() {
        let mut gen = IdentGen::new(0);

        let x = Identifier { path: vec![(1, 0), (1, 0)] };
        let y = Identifier { path: vec![(1, 0), (1, 1)] };
        gen.alloc(&x, &y);
        let b = gen.alloc(&x, &y);
        // println!("{:?} {:?} {:?}", x, b, y);
        assert!(x < b);
        assert!(b < y);
    }

    #[test]
    fn test_different_len_paths() {
        let mut gen = IdentGen::new(0);
        let x = Identifier { path: vec![(1, 0)] };
        let y = Identifier { path: vec![(1, 0), (15, 0)] };

        let z = gen.alloc(&x, &y);

        assert!(x < z);
        assert!(z < y);
    }

    #[test]
    fn test_alloc() {
        let mut gen = IdentGen::new(0);
        let a = Identifier { path: vec![(1, 0)] };
        let b = Identifier { path: vec![(3, 0)] };

        assert_eq!(gen.alloc(&a, &b), Identifier { path: vec![(2, 0)] });

        let c = Identifier { path: vec![(1, 0), (0, 0), (1, 0)] };
        let d = Identifier { path: vec![(1, 0), (0, 0), (3, 0)] };

        assert_eq!(gen.alloc(&c, &d), Identifier { path: vec![(1, 0), (0, 0), (2, 0)] });

        let e = Identifier { path: vec![(1, 0)] };
        let f = Identifier { path: vec![(2, 0)] };

        let res = gen.alloc(&e, &f);

        assert!(e < res);
        assert!(res < f);
        {
            let mut gen = IdentGen::new(1);

            let a = Identifier { path: vec![(4, 0), (4, 0)] };
            let b = Identifier { path: vec![(4, 0), (4, 0), (1, 1)] };

            let c = gen.alloc(&a, &b);
            assert!(a < c);
            assert!(c < b);
        }
        {
            let a = Identifier { path: vec![(5, 1), (6, 1), (6, 1), (6, 0)] };
            let b = Identifier { path: vec![(5, 1), (6, 1), (6, 1), (6, 0), (0, 0), (507, 0)] };

            let c = gen.alloc(&a, &b);
            assert!(a < c);
            assert!(c < b);
        }
    }

    #[test]
    fn test_index_in_range() {
        let mut gen = IdentGen::new(0);
        assert_eq!(gen.index_in_range(0, 1, 1), 0);
    }
}
