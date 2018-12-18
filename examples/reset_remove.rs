extern crate crdts;

use crdts::{CvRDT, CmRDT, Map, Orswot};

fn main() {
    let mut friend_map: Map<String, Orswot<String, u8>, u8> = Map::new();
    let add_ctx = friend_map.len()
        .derive_add_ctx(1);

    {
        let op = friend_map.update(
            "bob",
            add_ctx,
            |set, ctx| set.add("janet", ctx)
        );
        friend_map.apply(&op);
    }

    let mut friend_map_on_2nd_device = friend_map.clone();
    // the map on the 2nd devices adds to `bob`'s friend set
    {
        let device2_add_ctx = friend_map_on_2nd_device
            .len()
            .derive_add_ctx(2);
        let op = friend_map_on_2nd_device.update(
            "bob",
            device2_add_ctx,
            |set, c| set.add("erik", c)
        );
        friend_map_on_2nd_device.apply(&op);
    }
    // Meanwhile, the map on the first device removes
    // the entire 'bob' entry from the friend map.
    {
        let rm_ctx = friend_map
            .get(&"bob".to_string())
            .derive_rm_ctx();
        friend_map.rm("bob", rm_ctx);
    }

    // once these two devices synchronize...
    friend_map.merge(&friend_map_on_2nd_device);
    friend_map_on_2nd_device.merge(&friend_map);
    assert_eq!(friend_map, friend_map_on_2nd_device);
    
    // ... we see that "bob" is present but only
    // contains `erik`.
    //
    // This is because the `erik` entry was not
    // seen by the first device when it deleted
    // the entry.
    let bobs_friends: Vec<_> = friend_map   // Map<String, Orswot>
        .get(&"bob".to_string()).val // Option<Orswot>
        .unwrap()                    // Orswot
        .read().val                  // HashSet
        .into_iter()                 // Iter<Item=String>
        .collect();                  // Vec<String>

    assert_eq!(
        bobs_friends,
        vec!["erik".to_string()]
    );
}
