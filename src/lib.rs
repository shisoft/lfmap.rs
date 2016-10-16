#![feature(integer_atomics)]
#![feature(box_syntax)]
#![feature(core_intrinsics)]

extern crate libc;
extern crate core;

use std::hash::{BuildHasher, Hasher, BuildHasherDefault, Hash};
use core::intrinsics;
use std::marker::{PhantomData, Copy};
use std::mem;
use std::collections::hash_map::RandomState;
use std::borrow::Borrow;
use std::ptr;

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

pub struct HashMap<K, V, H = RandomState>
    where K: Hash + Eq + Copy, V: Copy, H: BuildHasher
{
    hasher_factory: H,
    table_addr: u64,
    entry_size: u64,

    kp: PhantomData<K>,
    vp: PhantomData<V>,

    pub capacity: u64
}

pub struct Entry<K, V> where K: Copy, V: Copy {
    key: K,
    tag: EntryTag,

    vp: PhantomData<V>
}

impl <K, V> Entry<K, V> where K: Copy, V: Copy {
    pub fn new_from(mem_ptr: u64) -> Option<Entry<K, V>> {
        unsafe {
            let mem_ptr = mem_ptr as usize;
            let kl = mem::size_of::<K>();
            let vl = mem::size_of::<V>();
            let tag = ptr::read((mem_ptr + kl + vl) as *mut u8);
            if tag == 0 {
                None
            } else {
                Some(
                    Entry {
                        tag: tag_from_num(tag),
                        key: ptr::read(mem_ptr as *mut K),

                        vp: PhantomData
                    }
                )
            }
        }
    }
    pub fn compare_and_swap(ptr: u64, old: V, new: V) -> V {
        let kl = mem::size_of::<K>() as u64;
        unsafe {
            let (val, ok) = intrinsics::atomic_cxchg_relaxed((ptr + kl) as *mut V, old, new);
            val
        }
    }
    pub fn load_val(ptr: u64) -> V {
        let kl = mem::size_of::<K>() as u64;
        unsafe {
            intrinsics::atomic_load_relaxed((ptr + kl) as *mut V)
        }
    }
    pub fn compare_and_swap_to(ptr: u64, new: V) -> V {
        let kl = mem::size_of::<K>();
        let ptr = ptr + kl as u64;
        unsafe {
            let mut old = intrinsics::atomic_load_relaxed(ptr as *mut V);
            loop {
                let (val, ok) = intrinsics::atomic_cxchg_relaxed(ptr as *mut V, old, new);
                if ok {
                    return old;
                } else {
                    old = val;
                }
            }
        }
    }
    pub fn to(&self, mem_ptr: u64, init: V) {
        unsafe {
            let mem_ptr = mem_ptr as usize;
            let kl = mem::size_of::<K>();
            Entry::<K, V>::set_tag(mem_ptr, &self.tag);
            ptr::write(mem_ptr as *mut K, self.key);
            ptr::write((mem_ptr + kl) as *mut V, init);
        }
    }
    pub fn set_tag(mem_ptr: usize, tag: &EntryTag) {
        let mem_ptr = mem_ptr;
        let kl = mem::size_of::<K>();
        let vl = mem::size_of::<V>();
        unsafe {
            ptr::write((mem_ptr + kl + vl) as *mut u8, num_from_tag(tag));
        }
    }
}

impl <K, V, H> HashMap<K, V, H>
    where K: Hash + Eq + Copy, V: Copy, H: BuildHasher
{
    pub fn with_options(opts: Options<H>) -> HashMap<K, V, H> {
        let kl = mem::size_of::<K>();
        let vl = mem::size_of::<V>();
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

            kp: PhantomData,
            vp: PhantomData
        }
    }
    pub fn new() -> HashMap<K, V> {
        HashMap::with_options(Options::default())
    }
    fn find(&self, k: K) -> (Option<Entry<K, V>>, u64) {
        let hash = self.hash(&k);
        let mut slot = self.table_slot(&hash);
        loop {
            let ptr = self.table_addr + slot * self.entry_size;
            let entry = Entry::<K, V>::new_from(ptr);
            match entry {
                Some(entry) => {
                    if entry.key != k {
                        slot += 1;
                    } else {
                        return (Some(entry), ptr)
                    }
                },
                None => return (None, ptr)
            }
        };
    }
    pub fn insert(&self, k: K, v: V) -> Option<V> {
        let (entry, ptr) = self.find(k);
        match entry {
            Some(entry) => {
                let old = Entry::<K, V>::compare_and_swap_to(ptr, v);
                Entry::<K, V>::set_tag(ptr as usize, &EntryTag::LIVE);
                return Some(old)
            },
            None => {
                let entry = Entry {
                    key: k,
                    tag: EntryTag::LIVE,

                    vp: PhantomData
                };
                entry.to(ptr, v);
                None
            }
        }
    }
    pub fn get(&self, k: K) -> Option<V> {
        let (entry, ptr) = self.find(k);
        match entry {
            Some(entry) => {
                match entry.tag {
                    EntryTag::Empty => None,
                    EntryTag::LIVE => Some(Entry::<K, V>::load_val(ptr)),
                    EntryTag::DEAD => None,
                    EntryTag::MOVED => None,
                }
            }
            None => None
        }
    }
    fn hash<Q: ?Sized>(&self, key: &Q) -> u64
        where K: Borrow<Q> + Hash + Eq, Q: Hash {
        let mut hasher = self.hasher_factory.build_hasher();
        key.hash(&mut hasher);
        hasher.finish()
    }
    pub fn table_slot(&self, hash: &u64) -> u64 {
        hash & (self.capacity - 1)
    }
}
