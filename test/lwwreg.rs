extern crate rand;

use quickcheck::{TestResult};
use crdts::{Error, LWWReg, FunkyCvRDT};


#[test]
fn test_default() {
    let reg: LWWReg<String, u64> = LWWReg::default();

    assert_eq!(reg, LWWReg { val: "".to_string(), marker: 0});
}

#[test]
fn test_update() {
    let mut reg = LWWReg {val: 123, marker: 0};

    // normal update: new marker is a descended of current marker
    // EXPECTED: success, the val and marker are update
    assert!(reg.update(32, 2).is_ok());
    assert_eq!(reg, LWWReg {val: 32, marker: 2});

    // stale update: new marker is an ancester of the current marker
    // EXPECTED: succes, no-op
    assert!(reg.update(57, 1).is_ok());
    assert_eq!(reg, LWWReg {val: 32, marker: 2});

    // redundant update: new marker and val is same as of the current state
    // EXPECTED: success, no-op
    assert!(reg.update(32, 2).is_ok());
    assert_eq!(reg, LWWReg {val: 32, marker: 2});

    // bad update: new marker same as of the current marker but not value
    // EXPECTED: error
    assert_eq!(reg.update(4000, 2), Err(Error::ConflictingMarker));
    assert_eq!(reg, LWWReg {val: 32, marker: 2});
}

fn build_from_prim(prim: (u8, u16)) -> LWWReg<u8, (u16, u8)> {
    // we make the marker a tuple so that we avoid conflicts
    LWWReg {
        val: prim.0,
        marker: (prim.1, prim.0)
    }
}

quickcheck! {
    fn prop_associative(r1_prim: (u8, u16), r2_prim: (u8, u16), r3_prim: (u8, u16)) -> TestResult {
        let mut r1 = build_from_prim(r1_prim);
        let mut r2 = build_from_prim(r2_prim);
        let r3 = build_from_prim(r3_prim);

        let has_conflicting_marker = (r1.marker == r2.marker && r1.val != r2.val)
            || (r1.marker == r3.marker && r1.val != r3.val)
            || (r2.marker == r3.marker && r2.val != r3.val);

        if has_conflicting_marker {
            return TestResult::discard();
        }

        let mut r1_snapshot = r1.clone();

        // (r1 ^ r2) ^ r3
        assert!(r1.merge(&r2).is_ok());
        assert!(r1.merge(&r3).is_ok());

        // r1 ^ (r2 ^ r3)
        assert!(r2.merge(&r3).is_ok());
        assert!(r1_snapshot.merge(&r2).is_ok());
        
        // (r1 ^ r2) ^ r3 = r1 ^ (r2 ^ r3)
        TestResult::from_bool(r1 == r1_snapshot)
    }
    
    fn prop_commutative(r1_prim: (u8, u16), r2_prim: (u8, u16)) -> TestResult {
        let mut r1 = build_from_prim(r1_prim);
        let mut r2 = build_from_prim(r2_prim);

        if r1.marker == r2.marker && r1.val != r2.val {
            return TestResult::discard();
        }
        let r1_snapshot = r1.clone();

        // r1 ^ r2
        assert!(r1.merge(&r2).is_ok());

        // r2 ^ r1
        assert!(r2.merge(&r1_snapshot).is_ok());

        // r1 ^ r2 = r2 ^ r1
        TestResult::from_bool(r1 == r2)
    }

    fn prop_idempotent(r_prim: (u8, u16)) -> bool {
        let mut r = build_from_prim(r_prim);
        let r_snapshot = r.clone();

        // r ^ r
        assert!(r.merge(&r_snapshot).is_ok());
        // r ^ r = r
        r == r_snapshot
    }
}
