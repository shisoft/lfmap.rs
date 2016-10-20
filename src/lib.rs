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
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicPtr, Ordering};
use std::thread;
use core::fmt::Display;

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

//enum EntryTag {
//    Empty,
//    LIVE,
//    DEAD,
//    MOVED
//}

struct Table {
    addr: u64,
    capacity: u64,
    obj_ptr: u64
}
impl Table {
    fn to_raw_addr(&self, mptr: usize) {
        unsafe {
            let u64_size = mem::size_of::<u64>();
            ptr::write(mptr as *mut u64, self.addr);
            ptr::write((mptr + u64_size) as *mut u64, self.capacity);
            ptr::write((mptr + u64_size + u64_size) as *mut u64, 0);
        }
    }
    fn to_raw(&self) -> u64 {
        unsafe {
            let u64_size = mem::size_of::<u64>();
            let mptr = libc::malloc(3 * u64_size) as usize;
            self.to_raw_addr(mptr);
            mptr as u64
        }
    }
    fn from_raw(ptr: &AtomicU64) -> Option<Table> {
        let u64_size = mem::size_of::<u64>();
        let mptr = ptr.load(Ordering::SeqCst) as usize;
        if mptr == 0 {
            None
        } else {
            Some(
                unsafe {
                    Table {
                        addr: ptr::read(mptr as *mut u64),
                        capacity: ptr::read((mptr + u64_size) as *mut u64),
                        obj_ptr: mptr as u64
                    }
                }
            )
        }
    }
    fn incr_contained(&self) -> u64 {
        unsafe {
            let u64_size = mem::size_of::<u64>() as u64;
            intrinsics::atomic_xadd((self.obj_ptr + u64_size * 2) as *mut u64, 1)
        }
    }
    fn contained(&self) -> u64 {
        unsafe {
            let u64_size = mem::size_of::<u64>() as u64;
            intrinsics::atomic_load((self.obj_ptr + u64_size * 2) as *mut u64)
        }
    }
}
pub struct HashMap<K, V, H = RandomState>
    where K: Hash + Eq + Copy, V: Copy, H: BuildHasher
{
    hasher_factory: H,
    curr_table: AtomicU64,
    prev_table: AtomicU64,
    entry_size: u64,

    kl: u64,
    vl: u64,

    resizing: AtomicBool,

    kp: PhantomData<K>,
    vp: PhantomData<V>,
}

pub struct Entry<K, V> where K: Copy, V: Copy {
    key: K,
    tag: u8,

    vp: PhantomData<V>
}

impl <K, V> Entry<K, V> where K: Copy, V: Copy {
    pub fn new_from(ptr: u64, kl: u64, vl: u64) -> Option<Entry<K, V>> {
        unsafe {
            let ptr = ptr as u64;
            let tag_ptr = ptr + kl + vl;
            let tag = intrinsics::atomic_load_relaxed(tag_ptr as *mut u8);
            if tag == 0 {
                None
            } else {
                Some(
                    Entry {
                        tag: tag,
                        key: ptr::read(ptr as *mut K),

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
    pub fn compare_and_swap_to(ptr: u64, new: V, kl: u64) -> V {
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
    fn set_tag(ptr: usize, tag: u8, kl: u64, vl: u64) {
        let kl = mem::size_of::<K>();
        let vl = mem::size_of::<V>();
        let tag_ptr = ptr + kl + vl;
        unsafe {
            intrinsics::atomic_store(tag_ptr as *mut u8, tag)
        }
    }
    fn cas_tag(ptr: u64, old: u8, new: u8, kl: u64, vl: u64) -> (u8, bool) {
        let tag_ptr = ptr + kl + vl;
        let old_byte = old;
        let new_byte = new;
        unsafe {
            intrinsics::atomic_cxchg_relaxed(tag_ptr as *mut u8, old_byte, new_byte)
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
fn is_power_of_2(num: u64) -> bool {
    if num < 1 {return false}
    if num <= 2 {return true}
    if num % 2 == 1 {return false};
    return is_power_of_2(num / 2);
}
impl <K, V, H> HashMap<K, V, H>
    where K: Hash + Eq + Copy + Send + Display, V: Copy + Send, H: BuildHasher + Send
{
    pub fn with_options(opts: Options<H>) -> HashMap<K, V, H> {
        if !is_power_of_2(opts.capacity) {
            panic!("Capacity must be power of 2 but got: {}", opts.capacity);
        }
        let kl = mem::size_of::<K>();
        let vl = mem::size_of::<V>();
        let tl = mem::size_of::<u8>();
        let entry_size = kl + vl + tl;
        let addr = new_table(entry_size as u64, opts.capacity);
        HashMap {
            curr_table: AtomicU64::new(Table{addr: addr, capacity: opts.capacity, obj_ptr: 0}.to_raw()),
            prev_table: AtomicU64::new(0),
            hasher_factory: opts.hasher_factory,
            entry_size: entry_size as u64,

            kl: kl as u64,
            vl: vl as u64,

            resizing: AtomicBool::new(false),

            kp: PhantomData,
            vp: PhantomData
        }
    }
    pub fn new() -> HashMap<K, V> {
        HashMap::with_options(Options::default())
    }
    fn find(&self, k: K, table_ptr: &AtomicU64) -> (Option<Entry<K, V>>, u64) {
        let table = Table::from_raw(table_ptr);
        match table {
            Some(table) => {
                let hash = self.hash(&k);
                let mut slot = self.table_slot(hash, &table);
                loop {
                    let ptr = table.addr + slot * self.entry_size;
                    let entry = Entry::<K, V>::new_from(ptr, self.kl, self.vl);
                    match entry {
                        Some(entry) => {
                            if entry.key != k {
                                slot = self.table_slot(slot + 1, &table);
                            } else {
                                return (Some(entry), ptr)
                            }
                        },
                        None => return (None, ptr)
                    }
                };
            }
            None => (None, 0)
        }
    }
    fn resize(&self) -> bool {
        if !self.resizing.compare_and_swap(false, true, Ordering::SeqCst) {
            assert_eq!(self.prev_table.load(Ordering::SeqCst), 0);
            let prev_table = Table::from_raw(&self.curr_table).unwrap();
            let new_capacity = prev_table.capacity * 2;
            let new_addr = new_table(self.entry_size, new_capacity);
            self.prev_table.store(self.curr_table.load(Ordering::SeqCst), Ordering::SeqCst);
            self.curr_table.store(Table{
                addr: new_addr,
                capacity: new_capacity,
                obj_ptr: 0
            }.to_raw(), Ordering::SeqCst);
            let new_table = Table::from_raw(&self.curr_table).unwrap();
            let mut prev_clear = true;
            loop {
                for slot in 0..prev_table.capacity {
                    let ptr = prev_table.addr + slot * self.entry_size;
                    let entry = Entry::<K, V>::new_from(ptr, self.kl, self.vl);
                    match entry {
                        Some(entry) => {
                            match entry.tag {
                                1 => {
                                    self.insert_(&new_table, entry.key, Some(Entry::<K, V>::load_val(ptr)), 1);
                                    Entry::<K, V>::set_tag(ptr as usize, 3, self.kl, self.vl);
                                    prev_clear = false;
                                }
                                _ => {},
                            }
                        },
                        None => {}
                    }
                }
                if prev_clear {
                    break;
                } else {
                    prev_clear = true;
                }
            }
            self.prev_table.store(0, Ordering::SeqCst);
            self.resizing.store(false, Ordering::SeqCst);
            unsafe {
                libc::free(prev_table.addr as *mut libc::c_void);
                libc::free(self.prev_table.load(Ordering::SeqCst) as *mut libc::c_void)
            }
            true
        } else {
            false
        }
    }
    fn set_entry_moved(&self, k: K) {
        if self.is_resizing() {
            let (entry, ptr) = self.find(k, &self.prev_table);
            match entry {
                Some(entry) => Entry::<K, V>::set_tag(ptr as usize, 3, self.kl, self.vl),
                None => {}
            }
        }
    }

    pub fn insert(&self, k: K, v: V) -> Option<V> {
        let mut table = Table::from_raw(&self.curr_table).unwrap();
        while table.contained() > table.capacity / 2  {
            self.resize();
            table = Table::from_raw(&self.curr_table).unwrap();
        }
        self.insert_(&table, k, Some(v), 1)
    }

    fn insert_(&self, table: &Table, k: K, v: Option<V>, tag: u8) -> Option<V> {
        let hash = self.hash(&k);
        let mut slot = self.table_slot(hash, &table);
        let mut result;
        loop {
            let ptr = table.addr + slot * self.entry_size;
            let entry = Entry::<K, V>::new_from(ptr, self.kl, self.vl);
            match entry {
                Some(entry) => {
                    if entry.key != k {
                        slot = self.table_slot(slot + 1, &table);
                        continue;
                    } else {
                        match v {
                            Some(v) => {
                                let old = Entry::<K, V>::compare_and_swap_to(ptr, v, self.kl);
                                result = Some(old);
                            },
                            None => {
                                result = self.get_from_entry_ptr(Some(entry), ptr);
                            }
                        }
                        Entry::<K, V>::set_tag(ptr as usize, tag, self.kl, self.vl);
                        break;
                    }
                },
                None => {
                    unsafe {
                        let (val, ok) = Entry::<K, V>::cas_tag(ptr, 0, 1, self.kl, self.vl);
                        if !ok {
                            slot = self.table_slot(slot + 1, &table);
                            continue;
                        }
                        ptr::write(ptr as *mut K, k);
                        match v {
                            Some(v) => ptr::write((ptr + self.kl) as *mut V, v),
                            None => {}
                        }
                    }
                    result = None;
                    break;
                }
            }
        };
        self.set_entry_moved(k);
        table.incr_contained();
        result
    }
    fn is_resizing(&self) -> bool {
        self.prev_table.load(Ordering::SeqCst) != 0
    }
    fn get_from_entry_ptr(&self, entry: Option<Entry<K, V>>, ptr: u64) -> Option<V> {
        match entry {
            Some(entry) => {
                match entry.tag {
                    1 => Some(Entry::<K, V>::load_val(ptr)),
                    _ => None,
                }
            },
            None => None
        }
    }
    pub fn get(&self, k: K) -> Option<V> {
        let read_current = || {
            let (entry, ptr) = self.find(k, &self.curr_table);
            self.get_from_entry_ptr(entry, ptr)
        };
        if self.is_resizing() {
            let (prev_entry, prev_ptr) = self.find(k, &self.prev_table);
            match prev_entry {
                None => read_current(),
                Some(prev_entry) => {
                    match prev_entry.tag {
                        3 | 0 => read_current(),
                        1 => {
                            self.get_from_entry_ptr(Some(prev_entry), prev_ptr)
                        }
                        _ => None
                    }
                }
            }
        } else {
            read_current()
        }
    }
    pub fn remove(&self, k: K) -> Option<V> {
        let curr_t_val = self.insert_(&Table::from_raw(&self.curr_table).unwrap(), k, None, 2);
        let mut prev_t_val = None;
        if self.is_resizing() {
            let prev_table = Table::from_raw(&self.prev_table);
            if prev_table.is_some() {
                prev_t_val = self.insert_(&prev_table.unwrap(), k, None, 3);
            }
        }
        if curr_t_val.is_some() {
            curr_t_val
        } else {
            prev_t_val
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
    fn table_slot(&self, hash: u64, table: &Table) -> u64 {
        hash & (table.capacity - 1)
    }
    pub fn capacity(&self) -> u64 {
        Table::from_raw(&self.curr_table).unwrap().capacity
    }
}