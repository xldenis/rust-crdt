use std::cmp::Ordering;
use std::collections::BTreeMap;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VClock<W: Ord>(BTreeMap<W, u64>);

impl<W: Ord> PartialOrd for VClock<W> {
    fn partial_cmp(&self, other: &VClock<W>) -> Option<Ordering> {
        if self == other {
            Some(Ordering::Equal)
        } else if other.0.iter().all(|(w, c)| self.contains_descendent_element(w, c)) {
            Some(Ordering::Greater)
        } else if self.0.iter().all(|(w, c)| other.contains_descendent_element(w, c)) {
            Some(Ordering::Less)
        } else {
            None
        }
    }
}

impl<W: Ord> VClock<W> {
    pub fn new() -> VClock<W> {
        VClock(BTreeMap::new())
    }

    pub fn witness(&mut self, witness: W, counter: u64) {
        if !self.contains_descendent_element(&witness, &counter) {
            self.0.insert(witness, counter);
        }
    }

    pub fn contains_descendent_element(&self, witness: &W, counter: &u64) -> bool {
        self.0.get(witness)
              .map(|our_counter| our_counter >= counter)
              .unwrap_or(false)
    }
}

#[test]
fn test_vclock_ordering() {
    assert!(VClock::<i8>::new() == VClock::new());

    let (mut a, mut b) = (VClock::new(), VClock::new());
    a.witness("A", 1);
    a.witness("A", 2);
    a.witness("A", 0);
    b.witness("A", 1);

    // a {A:2}
    // b {A:1}
    // expect: a dominates
    assert!(a > b);
    assert!(b < a);
    assert!(a != b);
    
    b.witness("A", 3);
    // a {A:2}
    // b {A:3}
    // expect: b dominates
    assert!(b > a);
    assert!(a < b);
    assert!(a != b);

    a.witness("B", 1);
    // a {A:2, B:1}
    // b {A:3}
    // expect: concurrent
    assert!(a != b);
    assert!(!(a > b));
    assert!(!(b > a));

    a.witness("A", 3);
    // a {A:3, B:1}
    // b {A:3}
    // expect: a dominates
    assert!(a > b);
    assert!(b < a);
    assert!(a != b);

    b.witness("B", 2);
    // a {A:3, B:1}
    // b {A:3, B:2}
    // expect: b dominates
    assert!(b > a);
    assert!(a < b);
    assert!(a != b);

    a.witness("B", 2);
    // a {A:3, B:2}
    // b {A:3, B:2}
    // expect: equal
    assert!(!(b > a));
    assert!(!(a > b));
    assert!(a == b);
}
