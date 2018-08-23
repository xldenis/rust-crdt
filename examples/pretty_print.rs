extern crate crdts;

use crdts::{CmRDT};

fn main() {
    let mut vclock = crdts::VClock::new();
    let _ = vclock.witness(31231, 2);
    let _ = vclock.witness(4829, 9);
    let _ = vclock.witness(87132, 32);
    println!("vclock: {}", vclock);


    let mut reg = crdts::MVReg::<String, u128>::new();

    let ctx = reg.context();
    let dot = ctx.inc(9742820);
    let dot = reg.set("some val", &dot);
    reg.apply(&dot).unwrap();
    
    println!("reg: {:?}", reg);
}
