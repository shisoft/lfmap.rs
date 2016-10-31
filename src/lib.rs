#![feature(core_intrinsics)]
#![feature(integer_atomics)]

extern crate libc;
extern crate core;

use core::intrinsics;
use std::ptr;
use std::sync::atomic::{AtomicU64, Ordering};
use std::{thread, time};

const INITIAL_CAPACITY :u64 = 32;
type KV = u64;
const KV_BYTES: usize = (64 / 8);
const KV_BYTES_U64: u64 = KV_BYTES as u64;


macro_rules! if_resizing {
    (
        $map: ident, $if_exp: expr, $else_exp: expr
    ) => (
        {
            let response;
            loop {
                let resizing_counter = $map.resizing.load(Ordering::SeqCst);
                if $map.prev_table.load(Ordering::SeqCst) != 0 && resizing_counter != 0 {
                    let prev_count = $map.resizing.compare_and_swap(resizing_counter, resizing_counter + 1, Ordering::SeqCst);
                    if prev_count != resizing_counter {
                        continue;
                    } else {
                        response = $if_exp;
                        $map.resizing.fetch_sub(1, Ordering::SeqCst);
                        break;
                    }
                } else {
                    response = $else_exp;
                    break;
                }
            }
            response
        }
    );
 }

//enum EntryTag {
//    Empty,
//    LIVE,
//    DEAD,
//    MOVED
//}

struct Table {
    body_addr: u64,
    capacity: u64,
    contained: u64,
    meta_addr: u64, // not in the memory

}
impl Table {
    fn to_raw(&self) -> u64 {
        unsafe {
            let mptr = libc::malloc(3 * KV_BYTES) as usize;
            ptr::write(mptr as *mut KV, self.body_addr);
            ptr::write((mptr + KV_BYTES) as *mut KV, self.capacity);
            ptr::write((mptr + KV_BYTES * 2) as *mut KV, self.contained);
            mptr as u64
        }
    }
    fn from_raw(ptr: &AtomicU64) -> Table {
        let mptr = ptr.load(Ordering::SeqCst) as usize;
        unsafe {
            Table {
                body_addr: ptr::read(mptr as *mut KV),
                capacity: ptr::read((mptr + KV_BYTES) as *mut KV),
                contained: ptr::read((mptr + KV_BYTES * 2) as *mut KV), 
                meta_addr: mptr as u64
            }
        }
    }
    fn incr_contained(&self) -> u64 {
        unsafe {
            intrinsics::atomic_xadd((self.meta_addr + KV_BYTES_U64 * 2) as *mut KV, 1)
        }
    }
    fn contained(&self) -> u64 {
        unsafe {
            intrinsics::atomic_load((self.meta_addr + KV_BYTES_U64 * 2) as *mut KV)
        }
    }
}

pub struct Entry {
    key: u64,
    val: u64,
    tag: u64,
}

impl Entry {
    fn new_from(ptr: u64) -> Option<Entry> {
        unsafe {
            let ptr = ptr as u64;
            let key = intrinsics::atomic_load(ptr as *mut KV);
            let val_ptr = ptr + KV_BYTES_U64;
            let val = intrinsics::atomic_load(val_ptr as *mut KV);
            if key == 0 || val == 0 {
                None
            } else {
                Some(
                    Entry {
                        tag: {
                            match val {
                                2 | 3 => val,
                                _ => 1,
                            }
                        },
                        key: key,
                        val: val
                    }
                )
            }
        }
    }
    fn cas_val(ptr: u64, old: KV, new: KV) -> (KV, bool) {
        unsafe {
            intrinsics::atomic_cxchg((ptr + KV_BYTES_U64) as *mut KV, old, new)
        }
    }
    fn set_val(ptr: u64, val: KV) {
        unsafe {
            intrinsics::atomic_store((ptr + KV_BYTES_U64) as *mut KV, val);
        }
    }
    fn cas_val_to(ptr: u64, new: KV) -> KV {
        let ptr = ptr + KV_BYTES_U64;
        unsafe {
            let mut old = intrinsics::atomic_load(ptr as *mut KV);
            loop {
                let (val, ok) = intrinsics::atomic_cxchg(ptr as *mut KV, old, new);
                if ok {
                    return old;
                } else {
                    old = val;
                }
            }
        }
    }
    fn load_val(ptr: u64) -> KV {
        unsafe {
            intrinsics::atomic_load_relaxed((ptr + KV_BYTES_U64) as *mut KV)
        }
    }
    fn cas_key(ptr: u64, old: KV, new:KV) -> (KV, bool) {
        unsafe {
            intrinsics::atomic_cxchg(ptr as *mut KV, old, new)
        }
    }
}

pub struct Map {
    curr_table: AtomicU64,
    prev_table: AtomicU64,
    entry_size: u64,

    resizing: AtomicU64,
}

fn new_table_body(entry_size: u64, capacity: u64) -> u64 {
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
impl Map {
    pub fn with_options(capacity: u64) -> Map {
        if !is_power_of_2(capacity) {
            panic!("Capacity must be power of 2 but got: {}", capacity);
        }
        let entry_size = KV_BYTES * 2;
        let table_body_addr = new_table_body(entry_size as u64, capacity);
        Map {
            curr_table: AtomicU64::new(
                Table{
                    body_addr: table_body_addr,
                    capacity: capacity,
                    meta_addr: 0,
                    contained: 0
                }.to_raw()
            ),
            prev_table: AtomicU64::new(0),
            entry_size: entry_size as u64,
            resizing: AtomicU64::new(0),
        }
    }
    pub fn new() -> Map {
        Map::with_options(INITIAL_CAPACITY)
    }
    fn current(&self) -> &AtomicU64 {
        &self.curr_table
    }
    fn find(&self, k: u64, table_ptr: &AtomicU64) -> (Option<Entry>, KV) {
        let table = Table::from_raw(table_ptr);
        let hash = k;
        let mut slot = self.table_slot(hash, &table);
        loop {
            let ptr = table.body_addr + slot * self.entry_size;
            let entry = Entry::new_from(ptr);
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
    fn resize(&self) -> bool {
        if self.resizing.compare_and_swap(0, 1, Ordering::SeqCst) == 0 {
            assert_eq!(self.prev_table.load(Ordering::SeqCst), 0);
            let prev_table = Table::from_raw(&self.curr_table);
            let new_capacity = prev_table.capacity * 2;
            let new_addr = new_table_body(self.entry_size, new_capacity);
            self.prev_table.store(self.curr_table.load(Ordering::SeqCst), Ordering::SeqCst);
            self.curr_table.store(
                Table{
                    body_addr: new_addr,
                    capacity: new_capacity,
                    contained: 0,
                    meta_addr: 0,
                }.to_raw(), Ordering::SeqCst);
            let new_table = Table::from_raw(&self.curr_table);
            let mut prev_clear = true;
            loop {
                for slot in 0..prev_table.capacity {
                    let ptr = prev_table.body_addr + slot * self.entry_size;
                    let entry = Entry::new_from(ptr);
                    match entry {
                        Some(entry) => {
                            match entry.tag {
                                1 => {
                                    self.insert_to_table(&new_table, entry.key, None, Some(Entry::load_val(ptr)));
                                    Entry::set_val(ptr, 3);
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
            while self.resizing.compare_and_swap(1, 0, Ordering::SeqCst) != 1 {}
            self.prev_table.store(0, Ordering::SeqCst);
            unsafe {
                libc::free(prev_table.body_addr as *mut libc::c_void);
                libc::free(prev_table.meta_addr as *mut libc::c_void);
            }
            true
        } else {
            thread::sleep(time::Duration::from_millis(1)); //weird, but essential
            false
        }
    }
    fn set_entry_moved(&self, k: KV) {
        if_resizing!(self, {
            let (entry, ptr) = self.find(k, &self.prev_table);
            match entry {
                Some(_) => Entry::set_val(ptr, 3),
                None => {}
            }
        }, {});
    }

    pub fn insert(&self, k: u64, v: u64) -> Option<KV> {
        if k == 0 {panic!("key: {} is reserved for internal use", k)}
        match v {
            0 | 2 | 3 => panic!("value: {} is reserved for internal use", v),
            _ => {}
        }
        let mut table = Table::from_raw(&self.current());
        while table.contained() > table.capacity / 2  {
            self.resize();
            table = Table::from_raw(&self.current());
        }
        self.insert_to_table(&table, k, None, Some(v))
    }
    fn insert_to_table(&self, table: &Table, k: KV, expected: Option<KV>, v: Option<KV>) -> Option<KV> {
        let hash = k;
        let mut slot = self.table_slot(hash, &table);
        let mut result = None;
        loop {
            let ptr = table.body_addr + slot * self.entry_size;
            let entry = Entry::new_from(ptr);
            match entry {
                Some(entry) => {
                    if entry.key != k {
                        slot = self.table_slot(slot + 1, &table);
                        continue;
                    } else {
                        match v {
                            Some(v) => {
                                match expected {
                                    None => {
                                        result = Some(Entry::cas_val_to(ptr, v));
                                    }
                                    Some(exp_v) => {
                                        let (pv, _) = Entry::cas_val(ptr, exp_v, v);
                                        result = Some(pv);
                                    }
                                }
                            },
                            None => {
                                result = Some(entry.val);
                            }
                        }
                        break;
                    }
                },
                None => {
                    match expected {
                        None | Some(0) => {
                            let (_, ok) = Entry::cas_key(ptr, 0, k);
                            if !ok {
                                slot = self.table_slot(slot + 1, &table);
                                continue;
                            }
                            match v {
                                Some(v) => {
                                    match expected {
                                        None => {
                                            Entry::set_val(ptr, v);
                                        },
                                        Some(0) => {
                                            let (prev, _) = Entry::cas_val(ptr, 0, v);
                                            result = Some(prev);
                                        }
                                        _ => {}
                                    }
                                },
                                None => {}
                            }
                            table.incr_contained();
                            break;
                        },
                        Some(_) => {return None;}
                    }
                }
            }
        };
        self.set_entry_moved(k);
        match result {
            None => None,
            Some(0) | Some(1) | Some(2) | Some(3) => None,
            _ => result,
        }
    }
    pub fn update_if(&self, k: KV, expected: KV, v: KV) -> Option<KV> {
        let update_current = |expected| {
            self.insert_to_table(&Table::from_raw(&self.curr_table), k, Some(expected), Some(v))
        };
        if_resizing!(self, {
            let (prev_entry, _) = self.find(k, &self.prev_table);
            match prev_entry {
                None => update_current(expected),
                Some(prev_entry) => {
                    match prev_entry.tag {
                        1 => {
                            let prev_val = prev_entry.val;
                            let mut curr_tb_prev = None;
                            if prev_val == expected {
                                curr_tb_prev = update_current(0);
                            }
                            match curr_tb_prev {
                                None | Some(0) => Some(prev_val),
                                Some(pv) => Some(pv)
                            }
                        }
                        _ => update_current(expected),
                    }
                }
            }
        }, {
            update_current(expected)
        })
    }
    pub fn compute<U: Fn(KV, KV) -> KV>(&self, k: KV, compute_val: U) -> Option<KV> {
        let mut val_opt = self.get(k);
        loop {
            match val_opt {
                Some(val) => {
                    let computed = compute_val(k, val);
                    let update_res = self.update_if(k, val, computed);
                    match update_res {
                        Some(update_res) => {
                            if update_res == val {
                                return Some(computed);
                            } else {
                                val_opt = Some(update_res);
                                continue;
                            }
                        },
                        None => {
                            return None;
                        }
                    }
                },
                None => {
                    return None;
                }
            }
        }
    }
    fn get_from_entry_ptr(&self, entry: Option<Entry>) -> Option<KV> {
        match entry {
            Some(entry) => {
                match entry.tag {
                    1 => Some(entry.val),
                    _ => None,
                }
            },
            None => None
        }
    }
    pub fn get(&self, k: KV) -> Option<KV> {
        let read_current = || {
            let (entry, _) = self.find(k, &self.current());
            self.get_from_entry_ptr(entry)
        };
        if_resizing!(self, {
            let (prev_entry, _) = self.find(k, &self.prev_table);
            match prev_entry {
                None => read_current(),
                Some(prev_entry) => {
                    match prev_entry.tag {
                        3 | 0 => read_current(),
                        1 => {
                            self.get_from_entry_ptr(Some(prev_entry))
                        }
                        _ => None
                    }
                }
            }
        }, {
            read_current()
        })
    }
    pub fn remove(&self, k: KV) -> Option<KV> {
        let curr_t_val = self.insert_to_table(&Table::from_raw(&self.current()), k, None, Some(2));
        let mut prev_t_val = None;
        if_resizing!(self, {
            let prev_table = Table::from_raw(&self.prev_table);
            prev_t_val = self.insert_to_table(&prev_table, k, None, Some(3));
        }, {});
        if curr_t_val.is_some() {
            curr_t_val
        } else {
            prev_t_val
        }
    }
    fn table_slot(&self, hash: u64, table: &Table) -> u64 {
        hash & (table.capacity - 1)
    }
    pub fn capacity(&self) -> u64 {
        Table::from_raw(&self.current()).capacity
    }
}
impl Drop for Map {
    fn drop(&mut self) {
        let curr_table = Table::from_raw(&self.curr_table);
        let have_prev_table = self.prev_table.load(Ordering::SeqCst) != 0;
        unsafe {
            if have_prev_table {
                let prev_table = Table::from_raw(&self.prev_table);
                libc::free(prev_table.body_addr as *mut libc::c_void);
                libc::free(prev_table.meta_addr as *mut libc::c_void);
            }
            libc::free(curr_table.body_addr as *mut libc::c_void);
            libc::free(curr_table.meta_addr as *mut libc::c_void);
        }
    }
}
