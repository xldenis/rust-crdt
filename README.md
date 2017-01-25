# rust-crdt
[![Build Status](https://travis-ci.org/spacejam/rust-crdt.svg?branch=master)](https://travis-ci.org/spacejam/rust-crdt)
[![crates.io](http://meritbadge.herokuapp.com/crdts)](https://crates.io/crates/crdts)

Thoroughly tested serializable practical CRDT's ported from riak_dt.


[documentation](https://docs.rs/crdts/1.2.11/crdts/)


- [x] Vector Clock
- [x] ORSWOT
- [x] LWW Register
- [x] G-Counter
- [ ] Top-K Set
- [ ] Map
- [ ] G-Set
- [ ] OR-Set
- [x] PN-Counter
- [ ] EM-Counter


## examples

### OR-Set Without Tombstones (ORSWOT)
```rust
let (mut a, mut b) = (Orswot::new(), Orswot::new());
a.add("value bar".to_string(), "witnessing node A".to_string());
assert_eq!(a.value(), vec!["value bar".to_string()]);
b.add("value baz".to_string(), "witnessing node B".to_string());
assert_eq!(b.value(), vec!["value baz".to_string()]);
let mut c = a.clone();
assert_eq!(c.value(), vec!["value bar".to_string()]);
c.merge(b);
assert_eq!(c.value(), vec!["value bar".to_string(), "value baz".to_string()]);
unsafe { a.remove("value bar".to_string()); }
let mut d = a.clone();
d.merge(c);
assert_eq!(d.value(), vec!["value baz".to_string()]);
```


If you want to learn about how CRDTs work, I suggest starting with the readme from [aphyr's meangirls](https://github.com/aphyr/meangirls) repo.
Afterwards, either check out the [riak dt](https://github.com/basho/riak_dt) source code or [A comprehensive study of CRDTs](https://hal.inria.fr/file/index/docid/555588/filename/techreport.pdf) depending on if you like to read papers or jump straight to source code examples.


### references

- [A comprehensive study of CRDTs](https://hal.inria.fr/file/index/docid/555588/filename/techreport.pdf)

- [riak dt - Convergent replicated datatypes in Erlang](https://github.com/basho/riak_dt)
