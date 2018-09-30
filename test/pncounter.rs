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

            results.insert(merged.value());
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
    assert_eq!(a.value(), 0);

    let op1 = a.inc("A".to_string());
    a.apply(&op1);
    assert_eq!(a.value(), 1);

    let op2 = a.inc("A".to_string());
    a.apply(&op2);
    assert_eq!(a.value(), 2);

    let op3 = a.dec("A".to_string());
    a.apply(&op3);
    assert_eq!(a.value(), 1);

    let op4 = a.inc("A".to_string());
    a.apply(&op4);
    assert_eq!(a.value(), 2);
}
