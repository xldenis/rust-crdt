extern crate crdts;

use std::collections::BTreeSet;

use crdts::{*, pncounter::{Op, Dir}};

const ACTOR_MAX: u8 = 11;

fn build_op(prims: (u8, u64, bool)) -> Op<u8> {
    let (actor, counter, dir_choice) = prims;
    Op {
        dot: Dot { actor, counter },
        dir: if dir_choice {
            Dir::Pos
        } else {
            Dir::Neg
        }
    }
}

quickcheck! {
    fn prop_merge_converges(op_prims: Vec<(u8, u64, bool)>) -> bool {
        let ops: Vec<Op<u8>> = op_prims.into_iter().map(build_op).collect();

        let mut results = BTreeSet::new();

        // Permute the interleaving of operations should converge.
        // Largely taken directly from orswot
        for i in 2..ACTOR_MAX {
            let mut witnesses: Vec<PNCounter<u8>> =
                (0..i).map(|_| PNCounter::new()).collect();
            for op in ops.iter() {
                let index = op.dot.actor as usize % i as usize;
                let witness = &mut witnesses[index];
                witness.apply(op);
            }
            let mut merged = PNCounter::new();
            for witness in witnesses.iter() {
                merged.merge(&witness);
            }

            results.insert(merged.read());
            if results.len() > 1 {
                println!("opvec: {:?}", ops);
                println!("results: {:?}", results);
                println!("witnesses: {:?}", &witnesses);
                println!("merged: {:?}", merged);
            }
        }
        results.len() == 1
    }
}

#[test]
fn test_basic() {
    let mut a = PNCounter::new();
    assert_eq!(a.read(), 0);

    a.apply_inc("A".to_string());
    assert_eq!(a.read(), 1);

    a.apply_inc("A".to_string());
    assert_eq!(a.read(), 2);

    a.apply_dec("A".to_string());
    assert_eq!(a.read(), 1);

    a.apply_inc("A".to_string());
    assert_eq!(a.read(), 2);
}
