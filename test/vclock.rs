extern crate crdts;

use crdts::*;

fn build_vclock(prims: Vec<u8>) -> VClock<u8> {
    let mut v = VClock::new();
    for actor in prims {
        let op = v.inc(actor);
        v.apply(&op);
    }
    v
}

quickcheck! {
    fn prop_from_iter_of_iter_is_nop(prims: Vec<u8>) -> bool {
        let clock = build_vclock(prims);
        clock == clock.clone().into_iter().collect()
    }

    fn prop_from_iter_order_of_dots_should_not_matter(dots: Vec<(u8, u64)>) -> bool {
        // TODO: is there a better way to check comutativity of dots?
        let reverse: VClock<u8> = dots.clone()
            .into_iter()
            .rev()
            .collect();
        let forward: VClock<u8> = dots
            .into_iter()
            .collect();

        reverse == forward
    }

    fn prop_from_iter_dots_should_be_idempotent(dots: Vec<(u8, u64)>) -> bool {
        let single: VClock<u8> = dots.clone()
            .into_iter()
            .collect();

        let double: VClock<u8> = dots.clone()
            .into_iter()
            .chain(dots.into_iter())
            .collect();

        single == double
    }

    fn prop_truncate_self_is_nop(prims: Vec<u8>) -> bool {
        let clock = build_vclock(prims);
        let mut clock_truncated = clock.clone();
        clock_truncated.truncate(&clock);

        clock_truncated == clock
    }

    fn prop_subtract_with_empty_is_nop(prims: Vec<u8>) -> bool {
        let clock = build_vclock(prims);
        let mut subbed  = clock.clone();
        subbed.subtract(&VClock::new());
        subbed == clock
    }

    fn prop_subtract_self_is_empty(prims: Vec<u8>) -> bool {
        let clock = build_vclock(prims);
        let mut subbed  = clock.clone();
        subbed.subtract(&clock);
        subbed == VClock::new()
    }
}

#[test]
fn test_subtract() {
    let mut a: VClock<u8> = vec![(1, 4), (2, 3), (5, 9)].into_iter().collect();
    let b: VClock<u8> = vec![(1, 5), (2, 3), (5, 8)].into_iter().collect();
    let expected: VClock<u8> = vec![(5, 9)].into_iter().collect();

    a.subtract(&b);

    assert_eq!(a, expected);
}

#[test]
fn test_merge() {
    let mut a: VClock<u8> = vec![(1, 1), (2, 2), (4, 4)].into_iter().collect();
    let b: VClock<u8> = vec![(3, 3), (4, 3)].into_iter().collect();
    a.merge(&b);
    
    let c: VClock<u8> = vec![(1, 1), (2, 2), (3, 3), (4, 4)].into_iter().collect();
    assert_eq!(a, c);
}

#[test]
fn test_merge_less_left() {
    let (mut a, mut b) = (VClock::new(), VClock::new());
    a.witness(5, 5);

    b.witness(6, 6);
    b.witness(7, 7);

    a.merge(&b);
    assert_eq!(a.get(&5), 5);
    assert_eq!(a.get(&6), 6);
    assert_eq!(a.get(&7), 7);
}

#[test]
fn test_merge_less_right() {
    let (mut a, mut b) = (VClock::new(), VClock::new());
    a.witness(6, 6);
    a.witness(7, 7);

    b.witness(5, 5);

    a.merge(&b);
    assert_eq!(a.get(&5), 5);
    assert_eq!(a.get(&6), 6);
    assert_eq!(a.get(&7), 7);
}

#[test]
fn test_merge_same_id() {
    let (mut a, mut b) = (VClock::new(), VClock::new());
    a.witness(1, 1);
    a.witness(2, 1);

    b.witness(1, 1);
    b.witness(3, 1);

    a.merge(&b);
    assert_eq!(a.get(&1), 1);
    assert_eq!(a.get(&2), 1);
    assert_eq!(a.get(&3), 1);
}

#[test]
fn test_vclock_ordering() {
    assert_eq!(VClock::<i8>::new(), VClock::new());

    let (mut a, mut b) = (VClock::new(), VClock::new());
    a.witness("A".to_string(), 1);
    a.witness("A".to_string(), 2);
    a.witness("A".to_string(), 0);
    b.witness("A".to_string(), 1);

    // a {A:2}
    // b {A:1}
    // expect: a dominates
    assert!(a > b);
    assert!(b < a);
    assert!(a != b);

    b.witness("A".to_string(), 3);
    // a {A:2}
    // b {A:3}
    // expect: b dominates
    assert!(b > a);
    assert!(a < b);
    assert!(a != b);

    a.witness("B".to_string(), 1);
    // a {A:2, B:1}
    // b {A:3}
    // expect: concurrent
    assert!(a != b);
    assert!(!(a > b));
    assert!(!(b > a));

    a.witness("A".to_string(), 3);
    // a {A:3, B:1}
    // b {A:3}
    // expect: a dominates
    assert!(a > b);
    assert!(b < a);
    assert!(a != b);

    b.witness("B".to_string(), 2);
    // a {A:3, B:1}
    // b {A:3, B:2}
    // expect: b dominates
    assert!(b > a);
    assert!(a < b);
    assert!(a != b);

    a.witness("B".to_string(), 2);
    // a {A:3, B:2}
    // b {A:3, B:2}
    // expect: equal
    assert!(!(b > a));
    assert!(!(a > b));
    assert_eq!(a, b);
}
