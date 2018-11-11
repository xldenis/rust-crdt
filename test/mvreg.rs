use crdts::{*, mvreg::Op};

use quickcheck::TestResult;

#[derive(Debug, Clone)]
struct TestReg {
    reg: MVReg<u8, u8>,
    ops: Vec<Op<u8, u8>>
}

#[test]
fn test_apply() {
    let mut reg = MVReg::new();
    let clock = VClock::from(Dot { actor: 2, counter: 1 });
    reg.apply(&Op::Put { clock: clock.clone(), val: 71 });
    let read_ctx = reg.read();
    assert_eq!(read_ctx.add_clock, clock);
    assert_eq!(read_ctx.val, vec![71]);
}

#[test]
fn test_set_should_not_mutate_reg() {
    let reg = MVReg::<u8, u8>::new();
    let ctx = reg.read().derive_add_ctx(1);
    let op = reg.write(32, ctx);
    assert_eq!(reg, MVReg::new());
    let mut reg = reg;
    reg.apply(&op);

    let read_ctx = reg.read();
    assert_eq!(read_ctx.val, vec![32]);
    assert_eq!(read_ctx.add_clock, VClock::from(Dot { actor: 1, counter: 1 }));
}

#[test]
fn test_concurrent_update_with_same_value_dont_collapse_on_merge() {
    // this is important to prevent because it breaks commutativity
    let mut r1: MVReg<u8, u8> = MVReg::new();
    let mut r2 = MVReg::new();

    let ctx_4 = r1.read().derive_add_ctx(4);
    let ctx_7 = r2.read().derive_add_ctx(7);

    let op1 = r1.write(23, ctx_4);
    let op2 = r2.write(23, ctx_7);
    r1.apply(&op1);
    r2.apply(&op2);

    r1.merge(&r2);

    let read_ctx = r1.read();
    assert_eq!(read_ctx.val, vec![23, 23]);
    assert_eq!(
        read_ctx.add_clock,
        vec![Dot::new(4, 1), Dot::new(7, 1)]
            .into_iter()
            .collect()
    );
}

#[test]
fn test_concurrent_update_with_same_value_dont_collapse_on_apply() {
    // this is important to prevent because it breaks commutativity
    let mut r1: MVReg<u8, u8> = MVReg::new();
    let r2 = MVReg::new();

    let ctx_4 = r1.read().derive_add_ctx(4);
    let ctx_7 = r2.read().derive_add_ctx(7);

    let op1 = r1.write(23, ctx_4);
    r1.apply(&op1);
    let op2 = r2.write(23, ctx_7);
    r1.apply(&op2);

    let read_ctx = r1.read();
    assert_eq!(read_ctx.val, vec![23, 23]);
    assert_eq!(
        read_ctx.add_clock,
        vec![Dot::new(4, 1), Dot::new(7, 1)]
            .into_iter()
            .collect()
    );
}

#[test]
fn test_multi_val() {
    let mut r1 = MVReg::<u8, u8>::new();
    let mut r2 = MVReg::<u8, u8>::new();
    
    let ctx_1 = r1.read().derive_add_ctx(1);
    let ctx_2 = r2.read().derive_add_ctx(2);

    let op1 = r1.write(32, ctx_1);
    let op2 = r2.write(82, ctx_2);

    r1.apply(&op1);
    r2.apply(&op2);

    r1.merge(&r2);
    let read_ctx = r1.read();
    
    assert!(
        read_ctx.val == vec![32, 82] || read_ctx.val == vec![82, 32]
    );
}

#[test]
fn test_op_commute_quickcheck1() {
    let mut reg1 = MVReg::new();
    let mut reg2 = MVReg::new();

    let op1 = Op::Put { clock: Dot { actor: 1, counter: 1 }.into(), val: 1 };
    let op2 = Op::Put { clock: Dot { actor: 2, counter: 1 }.into(), val: 2 };

    reg2.apply(&op2);
    reg2.apply(&op1);
    reg1.apply(&op1);
    reg1.apply(&op2);

    assert_eq!(reg1, reg2);
}

fn ops_are_not_compatible(opss: &[&Vec<(u8, u8)>]) -> bool {
    // We need to make sure that we never insert two different values with
    // the same actor version.
    for a_ops in opss.iter() {
        for b_ops in opss.iter().filter(|o| o != &a_ops) {
            let mut a_clock = VClock::new();
            let mut b_clock = VClock::new();
            for ((_, a_actor), (_, b_actor)) in a_ops.iter().zip(b_ops.iter()) {
                let a_clock_op = a_clock.inc(*a_actor);
                let b_clock_op = b_clock.inc(*b_actor);
                a_clock.apply(&a_clock_op);
                b_clock.apply(&b_clock_op);

                if b_clock.get(&a_actor) == a_clock.get(&a_actor) {
                    // this check is a bit broad as it's not a failure
                    // to insert the same value with the same actor version
                    // but for simplicity we reject those ops as well
                    return true;
                }
            }
        }
    }
    false
}

fn build_test_reg(prim_ops: Vec<(u8, u8)>) -> TestReg {
    let mut reg = MVReg::default();
    let mut ops = Vec::new();
    for (val, actor) in prim_ops {
        let ctx = reg.read().derive_add_ctx(actor);
        let op = reg.write(val, ctx);
        reg.apply(&op);
        ops.push(op);
    }
    TestReg { reg, ops }
}

quickcheck! {
    fn prop_set_with_ctx_from_read(r_ops: Vec<(u8, u8)>, a: u8) -> bool {
        let mut reg = build_test_reg(r_ops).reg;
        let write_ctx = reg.read().derive_add_ctx(a);
        let op = reg.write(23, write_ctx);
        reg.apply(&op);

        let next_read_ctx = reg.read();
        next_read_ctx.val == vec![23]
    }
    
    fn prop_merge_idempotent(r_ops: Vec<(u8, u8)>) -> bool {
        let mut r = build_test_reg(r_ops).reg;
        let r_snapshot = r.clone();

        r.merge(&r_snapshot);

        assert_eq!(r, r_snapshot);
        true
    }

    fn prop_merge_commutative(
        r1_ops: Vec<(u8, u8)>,
        r2_ops: Vec<(u8, u8)>
    ) -> TestResult {
        if ops_are_not_compatible(&[&r1_ops, &r2_ops]) {
            return TestResult::discard();
        }
        let r1 = build_test_reg(r1_ops);
        let r2 = build_test_reg(r2_ops);
        let mut r1 = r1.reg;
        let mut r2 = r2.reg;

        let r1_snapshot = r1.clone();
        r1.merge(&r2);
        r2.merge(&r1_snapshot);

        assert_eq!(r1, r2);
        TestResult::from_bool(true)
    }

    fn prop_merge_associative(
        r1_ops: Vec<(u8, u8)>,
        r2_ops: Vec<(u8, u8)>,
        r3_ops: Vec<(u8, u8)>
    ) -> TestResult {
        if ops_are_not_compatible(&[&r1_ops, &r2_ops, &r3_ops]) {
            return TestResult::discard();
        }
        let mut r1 = build_test_reg(r1_ops).reg;
        let mut r2 = build_test_reg(r2_ops).reg;
        let r3 = build_test_reg(r3_ops).reg;
        let r1_snapshot = r1.clone();
        
        // r1 ^ r2
        r1.merge(&r2);

        // (r1 ^ r2) ^ r3
        r1.merge(&r3);

        // r2 ^ r3
        r2.merge(&r3);

        // r1 ^ (r2 ^ r3)
        r2.merge(&r1_snapshot);

        assert_eq!(r1, r2);
        TestResult::from_bool(true)
    }

    fn prop_truncate(r_ops: Vec<(u8, u8)>) -> bool {
        let mut r = build_test_reg(r_ops).reg;
        let r_snapshot = r.clone();

        // truncating with the empty clock should be a nop
        r.truncate(&VClock::new());
        assert_eq!(r, r_snapshot);

        // truncating with the merge of all val clocks should give us
        // an empty register
        let clock = r.read().add_clock;
        r.truncate(&clock);
        assert_eq!(r, MVReg::new());
        true
    }

    fn prop_op_idempotent(r_ops: Vec<(u8, u8)>) -> TestResult {
        let test = build_test_reg(r_ops);
        let mut r = test.reg;
        let r_snapshot = r.clone();
        for op in test.ops.iter() {
            r.apply(op);
        }

        assert_eq!(r, r_snapshot);
        TestResult::from_bool(true)
    }


    fn prop_op_commutative(
        o1_ops: Vec<(u8, u8)>,
        o2_ops: Vec<(u8, u8)>
    ) -> TestResult {
        if ops_are_not_compatible(&[&o1_ops, &o2_ops]) {
            return TestResult::discard();
        }
        let o1 = build_test_reg(o1_ops);
        let o2 = build_test_reg(o2_ops);

        let mut r1 = o1.reg;
        let mut r2 = o2.reg;

        for op in o2.ops.iter() {
            r1.apply(op);
        }
        
        for op in o1.ops.iter() {
            r2.apply(op);
        }

        assert_eq!(r1, r2);
        TestResult::from_bool(true)
    }


    fn prop_op_associative(
        o1_ops: Vec<(u8, u8)>,
        o2_ops: Vec<(u8, u8)>,
        o3_ops: Vec<(u8, u8)>
    ) -> TestResult {
        if ops_are_not_compatible(&[&o1_ops, &o2_ops, &o3_ops]) {
            return TestResult::discard();
        }
        let o1 = build_test_reg(o1_ops);
        let o2 = build_test_reg(o2_ops);
        let o3 = build_test_reg(o3_ops);
        let mut r1 = o1.reg;
        let mut r2 = o2.reg;


        // r1 <- r2
        for op in o2.ops.iter() {
            r1.apply(op);
        }

        // (r1 <- r2) <- r3
        for op in o3.ops.iter() {
            r1.apply(op);
        }

        // r2 <- r3
        for op in o3.ops.iter() {
            r2.apply(op);
        }

        // (r2 <- r3) <- r1
        for op in o1.ops.iter() {
            r2.apply(op);
        }

        assert_eq!(r1, r2);
        TestResult::from_bool(true)
    }
}
