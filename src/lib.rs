#![feature(integer_atomics)]
#![feature(box_syntax)]
#![feature(core_intrinsics)]

extern crate libc;
extern crate core;

use std::hash::{BuildHasher, Hasher, BuildHasherDefault, Hash};

const INITIAL_CAPACITY :u64 = 32;

pub struct Options<H> {
    pub capacity: u64,
    pub hasher_factory: H
}

impl <H> Default for Options<H> where H: BuildHasher + Default {
    fn default() -> Options<H> {
        Options {
            capacity: INITIAL_CAPACITY,
            hasher_factory: Default::default()
        }
    }
}

pub enum EntryTag {
    Empty,
    LIVE,
    DEAD,
    MOVED
}

pub fn tag_from_num(tag: u8) -> EntryTag {
    match tag {
        0 => EntryTag::Empty,
        1 => EntryTag::LIVE,
        2 => EntryTag::DEAD,
        3 => EntryTag::MOVED,
        _ => EntryTag::Empty
    }
}

pub fn num_from_tag(tag: &EntryTag) -> u8 {
    match tag {
        &EntryTag::Empty   => 0,
        &EntryTag::LIVE    => 1,
        &EntryTag::DEAD    => 2,
        &EntryTag::MOVED   => 3
    }
}

macro_rules! defmap {
    (
        $($m:ident,$k: ty, $v: ty);*
    ) =>
    (
        $(
            pub mod $m {


                use core::intrinsics;
                use std::marker::PhantomData;
                use std::mem;
                use libc;
                use super::*;
                use std::hash::{BuildHasher, Hasher, BuildHasherDefault, Hash};
                use std::collections::hash_map::RandomState;
                use std::borrow::Borrow;
                use std::ptr;

                pub struct HashMap<H = RandomState> {
                    hasher_factory: H,
                    table_addr: u64,
                    entry_size: u64,

                    pub capacity: u64
                }

                pub struct Entry {
                    key: $k,
                    tag: EntryTag,
                }

                impl Entry {
                    pub fn from(mem_ptr: u64) -> Option<Entry> {
                        unsafe {
                            let mem_ptr = mem_ptr as usize;
                            let kl = mem::size_of::<$k>();
                            let vl = mem::size_of::<$v>();
                            let tag = ptr::read((mem_ptr + kl + vl) as *mut u8);
                            if tag == 0 {
                                None
                            } else {
                                Some(
                                    Entry {
                                        tag: tag_from_num(tag),
                                        key: ptr::read(mem_ptr as *mut $k),
                                    }
                                )
                            }
                        }
                    }
                    pub fn compare_and_swap(ptr: u64, old: $v, new: $v) -> $v {
                        let kl = mem::size_of::<$k>() as u64;
                        unsafe {
                            let (val, ok) = intrinsics::atomic_cxchg_relaxed((ptr + kl) as *mut $v, old, new);
                            val
                        }
                    }
                    pub fn load_val(ptr: u64) -> $v {
                        let kl = mem::size_of::<$k>() as u64;
                        unsafe {
                            intrinsics::atomic_load_relaxed((ptr + kl) as *mut $v)
                        }
                    }
                    pub fn compare_and_swap_to(ptr: u64, new: $v) -> $v {
                        let kl = mem::size_of::<$k>();
                        let ptr = ptr + kl as u64;
                        unsafe {
                            let mut old = intrinsics::atomic_load_relaxed(ptr as *mut $v);
                            loop {
                                let (val, ok) = intrinsics::atomic_cxchg_relaxed(ptr as *mut $v, old, new);
                                if ok {
                                    return old;
                                } else {
                                    old = val;
                                }
                            }
                        }
                    }
                    pub fn to(&self, mem_ptr: u64, init: $v) {
                        unsafe {
                            let mem_ptr = mem_ptr as usize;
                            let kl = mem::size_of::<$k>();
                            Entry::set_tag(mem_ptr, &self.tag);
                            ptr::write(mem_ptr as *mut $k, self.key);
                            ptr::write((mem_ptr + kl) as *mut $v, init);
                        }
                    }
                    pub fn set_tag(mem_ptr: usize, tag: &EntryTag) {
                        let mem_ptr = mem_ptr;
                        let kl = mem::size_of::<$k>();
                        let vl = mem::size_of::<$v>();
                        unsafe {
                            ptr::write((mem_ptr + kl + vl) as *mut u8, num_from_tag(tag));
                        }
                    }
                }

                impl <H> HashMap<H> where H: BuildHasher
                {
                    pub fn with_options(opts: Options<H>) -> HashMap<H> {
                       let kl = mem::size_of::<$k>();
                       let vl = mem::size_of::<$v>();
                       let tl = mem::size_of::<u8>();
                       let entry_size = kl + vl + tl;
                       let table_size = entry_size * opts.capacity as usize;
                       let addr = unsafe{libc::malloc(table_size)} as u64;
                       unsafe {
                           libc::memset(addr as *mut libc::c_void, 0, table_size);
                       }
                       HashMap {
                           table_addr: addr,
                           capacity: opts.capacity,
                           hasher_factory: opts.hasher_factory,
                           entry_size: entry_size as u64,
                       }
                    }
                    pub fn new() -> HashMap {
                       HashMap::with_options(Options::default())
                    }
                    pub fn insert(&self, k: $k, v: $v) -> Option<$v> {
                       let hash = self.hash(&k);
                       let mut slot = self.table_slot(&hash);
                       loop {
                           let ptr = self.table_addr + slot * self.entry_size;
                           let entry = Entry::from(ptr);
                           match entry {
                               Some(entry) => {
                                   if entry.key != k {
                                       slot += 1;
                                   } else {
                                       let old = Entry::compare_and_swap_to(ptr, v);
                                       Entry::set_tag(ptr as usize, &EntryTag::LIVE);
                                       return Some(old)
                                   }
                               },
                               None => {
                                   let entry = Entry {
                                       key: k,
                                       tag: EntryTag::LIVE,
                                   };
                                   entry.to(ptr, v);
                                   break;
                               }
                           }
                       }
                       None
                    }
                    pub fn get(&self, k: $k) -> Option<$v> {
                       let hash = self.hash(&k);
                       let mut slot = self.table_slot(&hash);
                       loop {
                           let ptr = self.table_addr + slot * self.entry_size;
                           let entry = Entry::from(ptr);
                           match entry {
                               Some(entry) => {
                                   if entry.key != k {
                                       slot += 1;
                                   } else {
                                       return {
                                            match entry.tag {
                                                EntryTag::Empty => None,
                                                EntryTag::LIVE => Some(Entry::load_val(ptr)),
                                                EntryTag::DEAD => None,
                                                EntryTag::MOVED => None,
                                            }
                                       }
                                   }
                               },
                               None => return None
                           }
                       }
                    }
                    fn hash<Q: ?Sized>(&self, key: &Q) -> u64
                            where $k: Borrow<Q> + Hash + Eq, Q: Hash {
                        let mut hasher = self.hasher_factory.build_hasher();
                        key.hash(&mut hasher);
                        hasher.finish()
                    }
                    pub fn table_slot(&self, hash: &u64) -> u64 {
                       hash & (self.capacity - 1)
                    }
                }
            }
        )*
    );
}

defmap!(
    u8_kv, u8, u8;
    u16_kv, u16, u16;
    u32_kv, u32, u32;
    u64_kv, u64, u64;

    i8_kv, i8, i8;
    i16_kv, i16, i16;
    i32_kv, i32, i32;
    i64_kv, i64, i64
);