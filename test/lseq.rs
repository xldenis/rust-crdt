
use crdts::lseq::*;
use crdts::lseq::ident::*;
use rand::distributions::Alphanumeric;
use rand::Rng;

#[test]
fn test_out_of_order_inserts() {
    let mut site1 = LSeq::new(0);
    site1.local_insert(0, 'a');
    site1.local_insert(1, 'c');
    site1.local_insert(1, 'b');

    assert_eq!(site1.sequence().collect::<String>(), "abc");
}

#[test]
fn test_inserts() {
    // A simple smoke test to ensure that insertions work properly.
    // Uses two sites which random insert a character and then immediately insert it into the
    // other site.
    let mut rng = rand::thread_rng();

    let mut s1 = rng.sample_iter(Alphanumeric);
    let mut s2 = rng.sample_iter(Alphanumeric);

    let mut site1 = LSeq::new(0);
    let mut site2 = LSeq::new(1);

    for _ in 0..5000 {
        if rng.gen() {
            let op = site1.local_insert(rng.gen_range(0, site1.raw_entries().len() + 1), s1.next().unwrap());
            site2.apply(&op);
        } else {
            let op = site2.local_insert(rng.gen_range(0, site2.raw_entries().len() + 1), s2.next().unwrap());
            site1.apply(&op);
        }
    }
    assert_eq!(site1.sequence().collect::<String>(), site2.sequence().collect::<String>());
}

#[derive(Clone)]
struct OperationList(pub Vec<Op<char>>);

use quickcheck::{Arbitrary, Gen};

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

        let mut site1 = LSeq::new(g.gen());
        let ops = (0..size)
            .map(|_| {
                if g.gen() || site1.len() == 0 {
                    site1.local_insert(g.gen_range(0, site1.len() + 1), g.gen())
                } else {
                    site1.local_delete(g.gen_range(0, site1.len()))
                }
            })
            .collect();
        OperationList(ops)
    }
    // implement shrinking ://
}

#[test]
fn prop_inserts_and_deletes() {
    let mut rng = quickcheck::StdThreadGen::new(1000);
    let mut op1 = OperationList::arbitrary(&mut rng).0.into_iter();
    let mut op2 = OperationList::arbitrary(&mut rng).0.into_iter();

    let mut site1 = LSeq::new(0);
    let mut site2 = LSeq::new(1);

    let mut s1_empty = false;
    let mut s2_empty = false;
    while !s1_empty && !s2_empty {
        if rng.gen() {
            match op1.next() {
                Some(o) => {
                    site1.apply(&o);
                    site2.apply(&o);
                }
                None => {
                    s1_empty = true;
                }
            }
        } else {
            match op2.next() {
                Some(o) => {
                    site1.apply(&o);
                    site2.apply(&o);
                }
                None => {
                    s2_empty = true;
                }
            }
        }
    }

    let site1_text = site1.sequence().collect::<String>();
    let site2_text = site2.sequence().collect::<String>();

    assert_eq!(site1_text, site2_text);
}

