extern crate crdts;

use crdts::{CmRDT};

fn main() {
    let mut vclock = crdts::VClock::new();
    let _ = vclock.witness(31231, 2);
    let _ = vclock.witness(4829, 9);
    let _ = vclock.witness(87132, 32);
    println!("vclock:\t{}", vclock);

    let mut reg = crdts::MVReg::<String, u128>::new();

    let op1 = reg.set("some val", reg.read().derive_add_ctx(9742820));
    let op2 = reg.set("some other val", reg.read().derive_add_ctx(648572));
    reg.apply(&op1);
    reg.apply(&op2);

    println!("reg:\t{}", reg);
}
