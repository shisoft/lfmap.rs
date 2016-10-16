#![feature(core_intrinsics)]

extern crate LFMap;
extern crate libc;
extern crate core;

use std::sync::atomic::{AtomicIsize, Ordering};
use std::mem;
use std::ptr;
use core::intrinsics;

#[test]
fn prim_test () {
    let map = LFMap::HashMap::<u32, u32>::new();
    map.insert(123, 456);
    map.insert(789, 101112);
    assert_eq!(map.get(123).unwrap(), 456);
    assert_eq!(map.get(789).unwrap(), 101112);
    map.insert(123, 123);
    //assert_eq!(map.get(123).unwrap(), 123);
}

#[test]
fn atom_test () {
    let some_isize = AtomicIsize::new(5);

    assert_eq!(some_isize.compare_and_swap(5, 10, Ordering::SeqCst), 5);
    assert_eq!(some_isize.load(Ordering::SeqCst), 10);

    assert_eq!(some_isize.compare_and_swap(6, 12, Ordering::SeqCst), 10);
    assert_eq!(some_isize.load(Ordering::SeqCst), 10);
}

#[test]
fn atom_ptr_test () {
    unsafe {
        let ptr = libc::malloc(mem::size_of::<AtomicIsize>());
        ptr::write(ptr as *mut isize, 5);
        assert_eq!(intrinsics::atomic_load_relaxed(ptr as *mut isize), 5);

        let (val, ok) = intrinsics::atomic_cxchg_relaxed(ptr as *mut isize, 5, 10);

        assert_eq!(ok, true);
        assert_eq!(val, 5);

        let (val, ok) = intrinsics::atomic_cxchg_relaxed(ptr as *mut isize, 5, 20);

        assert_eq!(ok, false);
        assert_eq!(val, 10);

        assert_eq!(intrinsics::atomic_load_relaxed(ptr as *mut isize), 10);
    }
}