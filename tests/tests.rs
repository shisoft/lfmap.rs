#![feature(core_intrinsics)]

extern crate lfmap;
extern crate libc;
extern crate core;

use std::sync::atomic::{AtomicIsize, Ordering};
use std::mem;
use std::ptr;
use core::intrinsics;
use std::thread;
use std::sync::Arc;

#[test]
fn prim_test () {
    let mut map = lfmap::HashMap::<u32, u32>::new();
    map.insert(123, 456);
    map.insert(789, 101112);
    assert_eq!(map.get(123).unwrap(), 456);
    assert_eq!(map.get(789).unwrap(), 101112);
    map.insert(123, 123);
    assert_eq!(map.get(123).unwrap(), 123);
    assert_eq!(map.remove(123).unwrap(), 123);
    assert!(map.get(123).is_none());
//    assert_eq!(map.compute(789, |_, v|{
//        v - 1000
//    }).unwrap(), 100112);
//    assert_eq!(map.get(789).unwrap(), 100112);
}

#[test]
fn resize () {
    let mut map = lfmap::HashMap::<u32, u32>::new();
    for i in 0..2048 {
        map.insert(i, i * 2);
    }
    for i in 0..2048 {
        match map.get(i) {
            Some(r) => assert_eq!(r, i * 2),
            None => panic!("{}, {}", i, map.capacity())
        }
    }
}

#[test]
fn parallel() {
    let map = Arc::new(lfmap::HashMap::<u64, u64>::new());
    let mut threads = vec![];
    for i in 0..9 {
        let map = map.clone();
        threads.push(
            thread::spawn(move || {
                for j in 0..40 {
                    map.insert(i + j * 10, i * j);
                }

            })
        );
    }
    for thread in threads {
        let _ = thread.join();
    }
//    for i in 0..9 {
//        for j in 0..40 {
//            assert_eq!(map.get(i + j * 10).unwrap(), i * j)
//        }
//    }
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