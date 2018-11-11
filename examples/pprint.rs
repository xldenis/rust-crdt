extern crate crdts;

use crdts::*;

fn main() {
    let mut vclock = VClock::new();
    let _ = vclock.apply_dot(Dot::new(31231, 2));
    let _ = vclock.apply_dot(Dot::new(4829, 9));
    let _ = vclock.apply_dot(Dot::new(87132, 32));
    println!("vclock:\t{}", vclock);

    let mut reg = MVReg::<String, u128>::new();

    let op1 = reg.write("some val", reg.read().derive_add_ctx(9742820));
    let op2 = reg.write("some other val", reg.read().derive_add_ctx(648572));
    reg.apply(&op1);
    reg.apply(&op2);

    println!("reg:\t{}", reg);
}
