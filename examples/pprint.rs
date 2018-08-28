extern crate crdts;

use crdts::{CmRDT};

fn main() {
    let mut vclock = crdts::VClock::new();
    let _ = vclock.witness(31231, 2);
    let _ = vclock.witness(4829, 9);
    let _ = vclock.witness(87132, 32);
    println!("vclock:\t{}", vclock);

    let mut reg = crdts::MVReg::<String, u128>::new();

    let ctx = reg.context();
    let dot_9742820 = ctx.inc(9742820);
    let dot_648572 = ctx.inc(648572);

    let op1 = reg.set("some val", &dot_9742820);
    let op2 = reg.set("some other val", &dot_648572);
    reg.apply(&op1).unwrap();
    reg.apply(&op2).unwrap();

    println!("reg:\t{}", reg);
}
