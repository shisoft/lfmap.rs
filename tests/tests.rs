extern crate lfmap;
use lfmap::*;

#[test]
pub fn will_not_overflow() {
    let table = Table::with_capacity(16);
    for i in 50..60 {
        assert_eq!(table.insert(i, i), None);
    }
    for i in 50..60 {
        assert_eq!(table.get(i), Some(i));
    }
    for i in 50..55 {
        assert_eq!(table.insert(i, 10), Some(i));
    }
    for i in 50..55 {
        assert_eq!(table.get(i), Some(10), "Check replace {}", i);
    }
}

//#![feature(core_intrinsics)]
//#![feature(test)]
//
//extern crate lfmap;
//extern crate libc;
//extern crate core;
//extern crate test;
//
//#[cfg(test)]
//mod tests {
//
//    use std::sync::atomic::{AtomicIsize, Ordering};
//    use std::mem;
//    use std::ptr;
//    use core::intrinsics;
//    use std::thread;
//    use std::sync::Arc;
//    use test::Bencher;
//    use lfmap;
//    use libc;
//
//    #[test]
//    fn prim_test () {
//        let map = lfmap::Map::new();
//        map.insert(123, 456);
//        map.insert(789, 101112);
//        assert_eq!(map.get(123).unwrap(), 456);
//        assert_eq!(map.get(789).unwrap(), 101112);
//        map.insert(123, 123);
//        assert_eq!(map.get(123).unwrap(), 123);
//        assert_eq!(map.remove(123).unwrap(), 123);
//        assert!(map.get(123).is_none());
//        assert_eq!(map.compute(789, |_, v|{
//            v - 1000
//        }).unwrap(), 100112);
//        assert_eq!(map.get(789).unwrap(), 100112);
//    }
//
//    #[test]
//    fn resize () {
//        let map = lfmap::Map::with_options(2);
//        for i in 5..2048 {
//            map.insert(i, i * 2);
//        }
//        for i in 5..2048 {
//            match map.get(i) {
//                Some(r) => assert_eq!(r, i * 2),
//                None => panic!("{}, {}", i, map.capacity())
//            }
//        }
//    }
//
//    #[test]
//    fn parallel_no_resize() {
//        let map = Arc::new(lfmap::Map::with_options(65536));
//        let mut threads = vec![];
//        for i in 5..99 {
//            map.insert(i, i * 10);
//        }
//        for i in 100..900 {
//            let map = map.clone();
//            threads.push(
//                thread::spawn(move || {
//                    for j in 5..60 {
//                        map.insert(i * 100 + j, i * j);
//                    }
//
//                })
//            );
//        }
//        for i in 5..9 {
//            for j in 1..10 {
//                map.remove(i * j);
//            }
//        }
//        for thread in threads {
//            let _ = thread.join();
//        }
//        for i in 100..900 {
//            for j in 5..60 {
//                assert_eq!(map.get(i * 100 + j).unwrap(), i * j)
//            }
//        }
//        for i in 5..9 {
//            for j in 1..10 {
//                assert!(map.get(i * j).is_none())
//            }
//        }
//    }
//
//    #[test]
//    fn parallel_with_resize() {
//        let map = Arc::new(lfmap::Map::with_options(32));
//        let mut threads = vec![];
//        for i in 5..24 {
//            let map = map.clone();
//            threads.push(
//                thread::spawn(move || {
//                    for j in 5..1000 {
//                        map.insert(i + j * 100, i * j);
//                    }
//
//                })
//            );
//        }
//        for thread in threads {
//            let _ = thread.join();
//        }
//        for i in 5..24 {
//            for j in 5..1000 {
//                let k = i + j * 100;
//                match map.get(k) {
//                    Some(v) => assert_eq!(v, i * j),
//                    None => {
//                        panic!("Value should not be None for key: {}", k)
//                    }
//                }
//            }
//        }
//    }
//
//    #[test]
//    fn parallel_hybird() {
//        let map = Arc::new(lfmap::Map::with_options(32));
//        for i in 5..128 {
//            map.insert(i, i * 10);
//        }
//        let mut threads = vec![];
//        for i in 256..265 {
//            let map = map.clone();
//            threads.push(
//                thread::spawn(move || {
//                    for j in 5..60 {
//                        map.insert(i * 10 + j , 10);
//                    }
//
//                })
//            );
//        }
//        for i in 5..8 {
//            let map = map.clone();
//            threads.push(
//                thread::spawn(move || {
//                    for j in 5..8 {
//                        map.remove(i * j);
//                    }
//                })
//            );
//        }
//        for thread in threads {
//            let _ = thread.join();
//        }
//        for i in 256..265 {
//            for j in 5..60 {
//                assert_eq!(map.get(i * 10 + j).unwrap(), 10)
//            }
//        }
//        for i in 5..8 {
//            for j in 5..8 {
//                match map.get(i * j) {
//                    Some(v) => {
//                        panic!("--- {}, {}, {} ---", v, i ,j);
//                    },
//                    None => {}
//                }
//            }
//        }
//    }
//
//    #[test]
//    fn parallel_hybird_pressure () {
//        for i in 0..100 {
//            parallel_with_resize();
//        }
//    }
//
//
//    #[test]
//    fn atom_test () {
//        let some_isize = AtomicIsize::new(5);
//
//        assert_eq!(some_isize.compare_and_swap(5, 10, Ordering::SeqCst), 5);
//        assert_eq!(some_isize.load(Ordering::SeqCst), 10);
//
//        assert_eq!(some_isize.compare_and_swap(6, 12, Ordering::SeqCst), 10);
//        assert_eq!(some_isize.load(Ordering::SeqCst), 10);
//    }
//
//    #[test]
//    fn atom_ptr_test () {
//        unsafe {
//            let ptr = libc::malloc(mem::size_of::<AtomicIsize>());
//            ptr::write(ptr as *mut isize, 5);
//            assert_eq!(intrinsics::atomic_load_relaxed(ptr as *mut isize), 5);
//
//            let (val, ok) = intrinsics::atomic_cxchg_relaxed(ptr as *mut isize, 5, 10);
//
//            assert_eq!(ok, true);
//            assert_eq!(val, 5);
//
//            let (val, ok) = intrinsics::atomic_cxchg_relaxed(ptr as *mut isize, 5, 20);
//
//            assert_eq!(ok, false);
//            assert_eq!(val, 10);
//
//            assert_eq!(intrinsics::atomic_load_relaxed(ptr as *mut isize), 10);
//        }
//    }
//
//    //mod compound_atomic { // failed experiment
//    //
//    //    use std::mem;
//    //    use core::intrinsics;
//    //    use libc;
//    //
//    //    #[test]
//    //    #[should_panic]
//    //    fn tuple () {
//    //        unsafe {
//    //            let example = (1 as u8, 2 as u16);
//    //            assert_eq!(mem::size_of_val(&example), mem::size_of::<u8>() + mem::size_of::<u16>());
//    //        }
//    //    }
//    //
//    //    pub struct ExpStruc<V> {
//    //        stat: u8,
//    //        val: V
//    //    }
//    //
//    //    #[test]
//    //    fn struc () {
//    //        assert_eq!(mem::size_of::<ExpStruc<u64>>(), mem::size_of::<u64>() * 2);
//    //        assert_eq!(mem::size_of::<ExpStruc<u32>>(), mem::size_of::<u32>() * 2);
//    //        assert_eq!(mem::size_of::<ExpStruc<u16>>(), mem::size_of::<u16>() * 2);
//    //        assert_eq!(mem::size_of::<ExpStruc<u8>>(), mem::size_of::<u8>() * 2);
//    //    }
//    //
//    //    pub enum Value<V> {
//    //        Empty,
//    //        Tombstone,
//    //        Moved,
//    //        Val(V),
//    //    }
//    //
//    //    #[test]
//    //    fn enums () {
//    //        assert_eq!(mem::size_of::<Value<u8>>(), mem::size_of:: <u8>() * 2);
//    //        assert_eq!(mem::size_of::<Value<u16>>(), mem::size_of::<u16>() * 2);
//    //        assert_eq!(mem::size_of::<Value<u32>>(), mem::size_of::<u32>() * 2);
//    //        assert_eq!(mem::size_of::<Value<u64>>(), mem::size_of::<u64>() * 2);
//    //    }
//    //
//    //    pub enum Value2 {
//    //        Tombstone,
//    //        Moved
//    //    }
//    //
//    //    #[test]
//    //    fn enums2 () {
//    //        assert_eq!(mem::size_of::<Value2>(), 1)
//    //    }
//    //
//    //    pub enum Value3<V> {
//    //        Tombstone(V),
//    //        Moved(V),
//    //        Val(V)
//    //    }
//    //
//    //    #[test]
//    //    fn enums3 () {
//    //        assert_eq!(mem::size_of::<Value3<u64>>(), mem::size_of::<u64>() * 2)
//    //    }
//    //
//    ////    #[test]
//    ////    fn atomic () {
//    ////        let size = mem::size_of::<Value<u32>>();
//    ////        let data = Value::Val(56);
//    ////        unsafe {
//    ////            let ptr = libc::malloc(size);
//    ////            let should_empty = intrinsics::atomic_load_relaxed(ptr as *mut f32);
//    ////        }
//    ////    }
//    //}
//}