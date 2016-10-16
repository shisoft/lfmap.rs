extern crate LFMap;

use std::collections::hash_map::RandomState;

#[test]
fn prim_test () {
    let map = LFMap::i32_kv::HashMap::<RandomState>::new();
    map.insert(123, 456);
    map.insert(789, 101112);
    assert_eq!(map.get(123).unwrap(), 456);
    assert_eq!(map.get(789).unwrap(), 101112);
}