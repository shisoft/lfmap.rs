#![feature(core_intrinsics)]
#![feature(integer_atomics)]

extern crate libc;
extern crate core;

use std::hash::{BuildHasher, Hasher, Hash};
use core::intrinsics;
use std::marker::{PhantomData, Copy};
use std::mem;
use std::collections::hash_map::RandomState;
use std::borrow::Borrow;
use std::ptr;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::thread;

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
pub struct Table {
    addr: u64,
    capacity: u64,
    contained: AtomicU64,
}
pub struct HashMap<K, V, H = RandomState>
    where K: Hash + Eq + Copy, V: Copy, H: BuildHasher
{
    hasher_factory: H,
    curr_table: Table,
    prev_table: Table,
    entry_size: u64,

    resizing: AtomicBool,

    kp: PhantomData<K>,
    vp: PhantomData<V>,
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
            let tag = intrinsics::atomic_load_relaxed((mem_ptr + kl + vl) as *mut u8);
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
    pub fn compare_and_swap(ptr: u64, old: V, new: V) -> (V, bool) {
        let kl = mem::size_of::<K>() as u64;
        unsafe {
            intrinsics::atomic_cxchg_relaxed((ptr + kl) as *mut V, old, new)
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
    pub fn set_tag(ptr: usize, tag: &EntryTag) {
        let kl = mem::size_of::<K>();
        let vl = mem::size_of::<V>();
        let tag_ptr = ptr + kl + vl;
        unsafe {
            intrinsics::atomic_store_relaxed(tag_ptr as *mut u8, num_from_tag(tag))
        }
    }
    pub fn cas_tag(ptr: usize, old: &EntryTag, new: &EntryTag) -> (EntryTag, bool) {
        let kl = mem::size_of::<K>();
        let vl = mem::size_of::<V>();
        let tag_ptr = ptr + kl + vl;
        let old_byte = num_from_tag(old);
        let new_byte = num_from_tag(new);
        unsafe {
            let (val, ok) = intrinsics::atomic_cxchg_relaxed(tag_ptr as *mut u8, old_byte, new_byte);
            (tag_from_num(val), ok)
        }
    }
}
fn new_table(entry_size: u64, capacity: u64) -> u64 {
    let table_size = (entry_size * capacity) as usize;
    let addr = unsafe{libc::malloc(table_size)} as u64;
    unsafe {
        libc::memset(addr as *mut libc::c_void, 0, table_size);
    }
    addr
}
impl <K, V, H> HashMap<K, V, H>
    where K: Hash + Eq + Copy + Send, V: Copy + Send, H: BuildHasher + Send
{
    pub fn with_options(opts: Options<H>) -> HashMap<K, V, H> {
        let kl = mem::size_of::<K>();
        let vl = mem::size_of::<V>();
        let tl = mem::size_of::<u8>();
        let entry_size = kl + vl + tl;
        let addr = new_table(entry_size as u64, opts.capacity);
        HashMap {
            curr_table: Table{addr: addr, capacity: opts.capacity, contained: AtomicU64::new(0)},
            prev_table: Table{addr: 0, capacity: 0, contained: AtomicU64::new(0)},
            hasher_factory: opts.hasher_factory,
            entry_size: entry_size as u64,

            resizing: AtomicBool::new(false),

            kp: PhantomData,
            vp: PhantomData
        }
    }
    pub fn new() -> HashMap<K, V> {
        HashMap::with_options(Options::default())
    }
    fn find(&self, k: K, table: &Table) -> (Option<Entry<K, V>>, u64) {
        let hash = self.hash(&k);
        let mut slot = self.table_slot(&hash, table) % table.capacity;
        loop {
            let ptr = table.addr + slot * self.entry_size;
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
    fn resize(&mut self) {
        let new_capacity = self.curr_table.capacity * 2;
        let new_addr = new_table(self.entry_size, new_capacity);
        self.prev_table = Table{
            addr: self.curr_table.addr,
            capacity: self.curr_table.capacity,
            contained: AtomicU64::new(self.curr_table.contained.load(Ordering::Relaxed))
        };
        self.curr_table = Table{
            addr: new_addr,
            capacity: new_capacity,
            contained: AtomicU64::new(0)
        };
        for slot in 0..self.prev_table.capacity {
            let ptr = self.prev_table.addr + slot * self.entry_size;
            let entry = Entry::<K, V>::new_from(ptr);
            match entry {
                Some(entry) => {
                    match entry.tag {
                        EntryTag::LIVE => {
                            self.insert(entry.key, Entry::<K, V>::load_val(ptr));
                            Entry::<K, V>::set_tag(ptr as usize, &EntryTag::MOVED);
                        }
                        _ => {},
                    }
                },
                None => {}
            }
        }
        unsafe {
            libc::free(self.prev_table.addr as *mut libc::c_void);
        }
        self.prev_table = Table{addr: 0, capacity: 0, contained: AtomicU64::new(0)};
        self.resizing.swap(false, Ordering::Relaxed);
    }
    fn put_new_entry(k: K, v: V, ptr: u64) {
        let entry = Entry {
            key: k,
            tag: EntryTag::LIVE,

            vp: PhantomData
        };
        entry.to(ptr, v);
    }
    fn set_entry_moved(&self, k: K) {
        if self.is_resizing() {
            let (entry, ptr) = self.find(k, &self.prev_table);
            match entry {
                Some(entry) => Entry::<K, V>::set_tag(ptr as usize, &EntryTag::MOVED),
                None => {}
            }
        }
    }
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        if self.curr_table.contained.load(Ordering::Relaxed) > self.curr_table.capacity / 2 {
            self.resize();
        }
        let (entry, ptr) = self.find(k, &self.curr_table);
        let result = {
            match entry {
                Some(_) => {
                    Entry::<K, V>::set_tag(ptr as usize, &EntryTag::LIVE);
                    let old = Entry::<K, V>::compare_and_swap_to(ptr, v);
                    return Some(old)
                },
                None => {
                    HashMap::<K, V>::put_new_entry(k, v, ptr);
                    None
                }
            }
        };
        self.set_entry_moved(k);
        self.curr_table.contained.fetch_add(1, Ordering::Relaxed);
        result
    }
    fn is_resizing(&self) -> bool {
        self.resizing.load(Ordering::Relaxed)
    }
    fn get_from_entry_ptr(&self, entry: Option<Entry<K, V>>, ptr: u64) -> Option<V> {
        match entry {
            Some(entry) => {
                match entry.tag {
                    EntryTag::Empty => None,
                    EntryTag::LIVE => Some(Entry::<K, V>::load_val(ptr)),
                    EntryTag::DEAD => None,
                    EntryTag::MOVED => None,
                }
            },
            None => None
        }
    }
    pub fn get(&self, k: K) -> Option<V> {
        if self.is_resizing() {
            let (prev_entry, prev_ptr) = self.find(k, &self.prev_table);
            let read_current = || {
                let (entry, ptr) = self.find(k, &self.curr_table);
                self.get_from_entry_ptr(entry, ptr)
            };
            match prev_entry {
                None => read_current(),
                Some(prev_entry) => {
                    match prev_entry.tag {
                        EntryTag::MOVED | EntryTag::Empty => read_current(),
                        EntryTag::LIVE => {
                            self.get_from_entry_ptr(Some(prev_entry), prev_ptr)
                        }
                        _ => None
                    }
                }
            }
        } else {
            let (entry, ptr) = self.find(k, &self.curr_table);
            self.get_from_entry_ptr(entry, ptr)
        }
    }
    pub fn remove(&self, k: K) -> Option<V> {
        let (entry, ptr) = if self.is_resizing() {
            self.find(k, &self.prev_table)
        } else {
            self.find(k, &self.curr_table)
        };
        match entry {
            Some(entry) => {
                match entry.tag {
                    EntryTag::LIVE => {
                        Entry::<K, V>::cas_tag(ptr as usize, &EntryTag::LIVE, &EntryTag::DEAD);
                        Some(Entry::<K, V>::load_val(ptr))
                    },
                    EntryTag::Empty => None,
                    EntryTag::DEAD => None,
                    EntryTag::MOVED => None,
                }
            }
            None => None
        }
    }
//    pub fn compute<U: Fn(K, V) -> V>(&self, k: K, compute_val: U) -> Option<V> {
//        let resizing = self.is_resizing();
//        let (entry, ptr) = if resizing {
//            self.find(k, &self.prev_table)
//        } else {
//            self.find(k, &self.curr_table)
//        };
//        let (curr_entry, curr_ptr) = if resizing {
//            self.find(k, &self.curr_table)
//        } else {
//            (entry, ptr)
//        };
//        match entry {
//            Some(entry) => {
//                match entry.tag {
//                    EntryTag::LIVE => {
//                        let old = Entry::<K, V>::load_val(ptr);
//                        loop {
//                            let new = compute_val(k, old);
//                            let (_, ok) = Entry::<K, V>::compare_and_swap(ptr, old, new);
//                            if ok {
//                                return Some(new)
//                            }
//                        }
//                    },
//                    EntryTag::Empty => None,
//                    EntryTag::DEAD => None,
//                    EntryTag::MOVED => None,
//                }
//            }
//            None => None
//        }
//    }
    fn hash<Q: ?Sized>(&self, key: &Q) -> u64
        where K: Borrow<Q> + Hash + Eq, Q: Hash {
        let mut hasher = self.hasher_factory.build_hasher();
        key.hash(&mut hasher);
        hasher.finish()
    }
    fn table_slot(&self, hash: &u64, table: &Table) -> u64 {
        hash & (table.capacity - 1)
    }
    pub fn capacity(&self) -> u64 {
        self.curr_table.capacity
    }
}
