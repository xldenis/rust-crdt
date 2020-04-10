use crdts::lseq::ident::*;
use crdts::lseq::*;
use crdts::CmRDT;
use rand::distributions::Alphanumeric;
use rand::Rng;

#[test]
fn test_new() {
    let site1: LSeq<char, SiteId> = LSeq::new(SiteId::new(0));
    assert_eq!(site1.len(), 0);
    assert!(site1.is_empty());
}

#[test]
fn test_is_empty() {
    let mut site1 = LSeq::new(SiteId::new(0));
    assert!(site1.is_empty());

    site1.insert_index(0, 'a');
    assert!(!site1.is_empty());
}

#[test]
fn test_out_of_order_inserts() {
    let mut site1 = LSeq::new(SiteId::new(0));
    site1.insert_index(0, 'a');
    site1.insert_index(1, 'c');
    site1.insert_index(1, 'b');

    assert_eq!(site1.iter().collect::<String>(), "abc");
}

#[test]
fn test_delete_of_index() {
    let mut site1 = LSeq::new(SiteId::new(0));
    site1.insert_index(0, 'a');
    site1.insert_index(1, 'b');
    assert_eq!(site1.iter().collect::<String>(), "ab");

    site1.delete_index(0);
    assert_eq!(site1.iter().collect::<String>(), "b");
}

#[test]
fn test_inserts() {
    // A simple smoke test to ensureethat insertions work properly.
    // Uses two sites which randomly insert a character and then immediately insert it into the
    // other site.
    let mut rng = rand::thread_rng();

    let mut s1 = rng.sample_iter(Alphanumeric);
    let mut s2 = rng.sample_iter(Alphanumeric);

    let mut site1 = LSeq::new(SiteId::new(0));
    let mut site2 = LSeq::new(SiteId::new(1));

    for _ in 0..5000 {
        if rng.gen() {
            let op = site1.insert_index(
                rng.gen_range(0, site1.raw_entries().len() + 1),
                s1.next().unwrap(),
            );
            site2.apply(op);
        } else {
            let op = site2.insert_index(
                rng.gen_range(0, site2.raw_entries().len() + 1),
                s2.next().unwrap(),
            );
            site1.apply(op);
        }
    }
    assert_eq!(
        site1.iter().collect::<String>(),
        site2.iter().collect::<String>()
    );
}

#[test]
fn test_insert_followed_by_deletes() {
    let mut rng = rand::thread_rng();

    let mut s1 = rng.sample_iter(Alphanumeric);

    let mut site1 = LSeq::new(SiteId::new(0));
    let mut site2 = LSeq::new(SiteId::new(1));

    for _ in 0..5000 {
        let c = s1.next().unwrap();
        let ix = rng.gen_range(0, site1.raw_entries().len() + 1);
        let insert_op = site1.insert_index(ix, c);
        site2.apply(insert_op);

        let delete_op =
            site2
                .delete_index(ix)
                .expect(&format!("ix@{} was out of bounds@{}", ix, site2.len()));
        site1.apply(delete_op);
    }

    assert!(
        site1.is_empty(),
        "site1 was not empty: {}",
        site1.iter().collect::<String>()
    );
    assert!(
        site2.is_empty(),
        "site2 was not empty: {}",
        site2.iter().collect::<String>()
    );
}

#[derive(Debug, Clone)]
struct OperationList(pub Vec<Op<char, SiteId>>);

use quickcheck::{Arbitrary, Gen, TestResult};

impl Arbitrary for OperationList {
    fn arbitrary<G: Gen>(g: &mut G) -> OperationList {
        let size = {
            let s = g.size();
            if s == 0 {
                0
            } else {
                g.gen_range(0, s)
            }
        };

        let mut site1 = LSeq::new(SiteId::new(g.gen()));
        let ops = (0..size)
            .filter_map(|_| {
                if g.gen() || site1.len() == 0 {
                    site1.delete_index(g.gen_range(0, site1.len() + 1))
                } else {
                    site1.delete_index(g.gen_range(0, site1.len()))
                }
            })
            .collect();
        OperationList(ops)
    }
    // implement shrinking ://
}

quickcheck! {
    fn prop_inserts_and_deletes(op1: OperationList, op2: OperationList) -> TestResult {
        let mut rng = quickcheck::StdThreadGen::new(1000);
        let mut op1 = op1.0.into_iter();
        let mut op2 = op2.0.into_iter();

        let mut site1 = LSeq::new(SiteId::new(0));
        let mut site2 = LSeq::new(SiteId::new(1));

        let mut s1_empty = false;
        let mut s2_empty = false;
        while !s1_empty && !s2_empty {
            if rng.gen() {
                match op1.next() {
                    Some(o) => {
                        site1.apply(o.clone());
                        site2.apply(o);
                    }
                    None => {
                        s1_empty = true;
                    }
                }
            } else {
                match op2.next() {
                    Some(o) => {
                        site1.apply(o.clone());
                        site2.apply(o);
                    }
                    None => {
                        s2_empty = true;
                    }
                }
            }
        }

        let site1_text = site1.iter().collect::<String>();
        let site2_text = site2.iter().collect::<String>();

        TestResult::from_bool(site1_text == site2_text)
    }

    fn prop_ops_are_idempotent(ops: OperationList) -> TestResult {
        let mut site1 = LSeq::new(SiteId::new(0));
        let mut site2 = LSeq::new(SiteId::new(1));

        for op in ops.0.into_iter() {
            // Apply the same op twice to site1
            site1.apply(op.clone());
            site1.apply(op.clone());

            // But only apply that op once to site2
            site2.apply(op);
        }

        let site1_text = site1.iter().collect::<String>();
        let site2_text = site2.iter().collect::<String>();

        TestResult::from_bool(site1_text == site2_text)
    }

    fn prop_len_is_proportional_to_ops(oplist: OperationList) -> TestResult {
        let mut expected_len = 0;
        let mut site1 = LSeq::new(SiteId::new(0));

        for op in oplist.0.into_iter() {
            match op {
                Op::Insert { .. } => expected_len += 1,
                Op::Delete { .. } => expected_len -= 1,
            };
            site1.apply(op);
        }

        TestResult::from_bool(site1.len() == expected_len)
    }
}
