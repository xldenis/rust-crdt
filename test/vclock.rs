extern crate crdts;

use crdts::*;

fn build_vclock(prims: Vec<u8>) -> VClock<u8> {
    let mut v = VClock::new();
    for actor in prims {
        v.apply_inc(actor);
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
            .map(|(a, c)| Dot::new(a, c))
            .rev()
            .collect();
        let forward: VClock<u8> = dots
            .into_iter()
            .map(|(a, c)| Dot::new(a, c))
            .collect();

        reverse == forward
    }

    fn prop_from_iter_dots_should_be_idempotent(dots: Vec<(u8, u64)>) -> bool {
        let single: VClock<u8> = dots.clone()
            .into_iter()
            .map(|(a, c)| Dot::new(a, c))
            .collect();

        let double: VClock<u8> = dots.clone()
            .into_iter()
            .chain(dots.into_iter())
            .map(|(a, c)| Dot::new(a, c))
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
    let mut a: VClock<u8> = vec![Dot::new(1, 4), Dot::new(2, 3), Dot::new(5, 9)]
        .into_iter()
        .collect();
    let b: VClock<u8> = vec![Dot::new(1, 5), Dot::new(2, 3), Dot::new(5, 8)]
        .into_iter()
        .collect();
    let expected: VClock<u8> = vec![Dot::new(5, 9)]
        .into_iter()
        .collect();

    a.subtract(&b);
    assert_eq!(a, expected);
}

#[test]
fn test_merge() {
    let mut a: VClock<u8> = vec![Dot::new(1, 1), Dot::new(4, 4)]
        .into_iter()
        .collect();
    let b: VClock<u8> = vec![Dot::new(3, 3), Dot::new(4, 3)]
        .into_iter()
        .collect();

    a.merge(&b);
    
    let expected: VClock<u8> = vec![Dot::new(1, 1), Dot::new(3, 3), Dot::new(4, 4)]
        .into_iter()
        .collect();

    assert_eq!(a, expected);
}

#[test]
fn test_merge_less_left() {
    let (mut a, mut b) = (VClock::new(), VClock::new());
    a.apply_dot(Dot::new(5, 5));

    b.apply_dot(Dot::new(6, 6));
    b.apply_dot(Dot::new(7, 7));

    a.merge(&b);
    assert_eq!(a.get(&5), 5);
    assert_eq!(a.get(&6), 6);
    assert_eq!(a.get(&7), 7);
}

#[test]
fn test_merge_less_right() {
    let (mut a, mut b) = (VClock::new(), VClock::new());
    a.apply_dot(Dot::new(6, 6));
    a.apply_dot(Dot::new(7, 7));

    b.apply_dot(Dot::new(5, 5));

    a.merge(&b);
    assert_eq!(a.get(&5), 5);
    assert_eq!(a.get(&6), 6);
    assert_eq!(a.get(&7), 7);
}

#[test]
fn test_merge_same_id() {
    let (mut a, mut b) = (VClock::new(), VClock::new());
    a.apply_dot(Dot::new(1, 1));
    a.apply_dot(Dot::new(2, 1));

    b.apply_dot(Dot::new(1, 1));
    b.apply_dot(Dot::new(3, 1));

    a.merge(&b);
    assert_eq!(a.get(&1), 1);
    assert_eq!(a.get(&2), 1);
    assert_eq!(a.get(&3), 1);
}

#[test]
fn test_vclock_ordering() {
    assert_eq!(VClock::<i8>::new(), VClock::new());

    let (mut a, mut b) = (VClock::new(), VClock::new());
    a.apply_dot(Dot::new("A".to_string(), 1));
    a.apply_dot(Dot::new("A".to_string(), 2));
    a.apply_dot(Dot::new("A".to_string(), 0));
    b.apply_dot(Dot::new("A".to_string(), 1));

    // a {A:2}
    // b {A:1}
    // expect: a dominates
    assert!(a > b);
    assert!(b < a);
    assert!(a != b);

    b.apply_dot(Dot::new("A".to_string(), 3));
    // a {A:2}
    // b {A:3}
    // expect: b dominates
    assert!(b > a);
    assert!(a < b);
    assert!(a != b);

    a.apply_dot(Dot::new("B".to_string(), 1));
    // a {A:2, B:1}
    // b {A:3}
    // expect: concurrent
    assert!(a != b);
    assert!(!(a > b));
    assert!(!(b > a));

    a.apply_dot(Dot::new("A".to_string(), 3));
    // a {A:3, B:1}
    // b {A:3}
    // expect: a dominates
    assert!(a > b);
    assert!(b < a);
    assert!(a != b);

    b.apply_dot(Dot::new("B".to_string(), 2));
    // a {A:3, B:1}
    // b {A:3, B:2}
    // expect: b dominates
    assert!(b > a);
    assert!(a < b);
    assert!(a != b);

    a.apply_dot(Dot::new("B".to_string(), 2));
    // a {A:3, B:2}
    // b {A:3, B:2}
    // expect: equal
    assert!(!(b > a));
    assert!(!(a > b));
    assert_eq!(a, b);
}
