extern crate crdts;
use crdts::{GCounter, CmRDT};

#[test]
fn test_basic() {
    let mut a = GCounter::new();
    let mut b = GCounter::new();
    let a_op = a.inc("A".to_string());
    let b_op = b.inc("B".to_string());
    a.apply(&a_op);
    b.apply(&b_op);
    assert_eq!(a.value(), b.value());
    assert!(a == b);
    
    let a_op2 = a.inc("A".to_string());
    a.apply(&a_op2);

    assert!(a.value() > b.value());
}
