#![no_std]
#![feature(allocator_api)]
#![feature(core_intrinsics)]
extern crate alloc;

// usize to usize lock-free, wait free table

use alloc::alloc::Global;
use core::alloc::{Alloc, Layout};
use core::{mem, ptr, intrinsics};
use core::sync::atomic::{AtomicUsize, AtomicPtr};
use core::sync::atomic::Ordering::Relaxed;
use core::iter::Copied;

type EntryTemplate = (usize, usize);

const EMPTY_KEY: usize = 0;
const EMPTY_VALUE: usize = 0;
const SENTINEL_VALUE: usize = 1;

struct Value {
    raw: usize,
    parsed: ParsedValue
}

enum ParsedValue {
    Val(usize),
    Prime(usize),
    Sentinel,
    Empty
}

enum ModResult {
    Replaced(usize),
    Fail(usize),
    Sentinel,
    NotFound,
    Done
}

enum ModOp {
    Insert(usize),
    Sentinel,
    Empty
}

pub struct Table {
    cap: AtomicUsize,
    chunk: AtomicUsize,
    new_chunk: AtomicUsize,
    occupation: AtomicUsize,
    val_bit_mask: usize, // 0111111..
    inv_bit_mask: usize  // 1000000..
}

impl Table {
    pub fn with_capacity(cap: usize) -> Self {
        if !is_power_of_2(cap) {
            panic!("capacity is not power of 2");
        }
        // Each entry key value pair is 2 words
        let chunk_size = cap * mem::size_of::<EntryTemplate>();
        let align = mem::align_of::<EntryTemplate>();
        let layout = Layout::from_size_align(chunk_size, align).unwrap();
        let chunk = unsafe { Global.alloc(layout) }.unwrap().as_ptr() as usize;
        // steal 1 bit in the MSB of value indicate Prime(1)
        let val_bit_mask = !0 << 1 >> 1;
        Self {
            cap: AtomicUsize::new(cap),
            chunk: AtomicUsize::new(chunk),
            new_chunk: AtomicUsize::new(chunk),
            occupation: AtomicUsize::new(0),
            val_bit_mask,
            inv_bit_mask: !val_bit_mask
        }
    }

    pub fn new() -> Self {
        Self::with_capacity(64)
    }

    pub fn get(&self, key: usize) -> Option<usize> {

        let mut base = self.chunk.load(Relaxed);
        loop {
            let val = self.get_from_chunk(base, key);
            match val.parsed {
                ParsedValue::Prime(val) | ParsedValue::Val(val) => return Some(val),
                ParsedValue::Sentinel => {
                    let new_chunk = self.new_chunk.load(Relaxed);
                    debug_assert_ne!(new_chunk, 0);
                    debug_assert_ne!(base, new_chunk);
                    base = new_chunk;
                }
                ParsedValue::Empty => return None
            }
        }
    }

    pub fn insert(&self, key: usize, value: usize) -> Option<usize> {
        let new_chunk = self.new_chunk.load(Relaxed);
        let old_chunk = self.chunk.load(Relaxed);
        let copying = new_chunk != old_chunk;
        let value_insertion = self.modify_entry(new_chunk, key, ModOp::Insert(value));
        let mut result = None;
        match value_insertion {
            ModResult::Done => {},
            ModResult::Replaced(v) => {
                result = Some(v)
            }
            ModResult::Fail(v) => {
                // don't handle failure by return the value
                return Some(v);
            }
            _ => unreachable!()
        };
        if copying {
            self.modify_entry(old_chunk, key, ModOp::Sentinel);
        }
        result
    }

    pub fn remove(&self, key: usize) -> Option<usize> {
        let new_chunk = self.new_chunk.load(Relaxed);
        let old_chunk = self.chunk.load(Relaxed);
        let copying = new_chunk != old_chunk;
        let res = self.modify_entry(new_chunk, key, ModOp::Empty);
        if copying {
            self.modify_entry(new_chunk, key, ModOp::Sentinel);
        }
        match res {
            ModResult::Replaced(v) => Some(v),
            _ => None
        }
    }

    fn get_from_chunk(&self, base: usize, key: usize) -> Value {
        let size = self.cap.load(Relaxed);
        let mut idx = key;
        let entry_size = mem::size_of::<EntryTemplate>();
        let cap = self.cap.load(Relaxed);
        let mut counter = 0;
        while counter < cap {
            idx &= (size - 1);
            let addr = base + idx * entry_size;
            let k = self.get_key(addr);
            if k == key {
                let val_res = self.get_value(addr);
                match val_res.parsed {
                    ParsedValue::Empty => {},
                    _ => return val_res
                }
            }
            if k == EMPTY_KEY {
                return Value::new(0, self);
            }
            idx += 1; // reprobe
            counter += 1;
        }

        // not found
        return Value::new(0, self);
    }

    fn modify_entry(&self, base: usize, key: usize, op: ModOp) -> ModResult {
        let mut idx = key;
        let cap = self.cap.load(Relaxed);
        let entry_size = mem::size_of::<EntryTemplate>();
        let mut replaced = None;
        let mut count = 0;
        while count <= cap {
            idx &= (cap - 1);
            let addr = base + idx * entry_size;
            let k = self.get_key(addr);
            if k == key {
                let val = self.get_value(addr);
                match &val.parsed {
                    ParsedValue::Val(v) | ParsedValue::Prime(v) => {
                        match op {
                            ModOp::Sentinel => {
                                self.set_sentinel(addr);
                                return ModResult::Done;
                            }
                            ModOp::Empty | ModOp::Insert(_) => {
                                if !self.set_tombstone(addr, val.raw) {
                                    // this insertion have conflict with others, abort
                                    return ModResult::Fail(*v);
                                } else {
                                    // we have put tombstone on the value
                                    replaced = Some(*v);
                                }
                            }
                        }
                        match op {
                            ModOp::Empty => {
                                return ModResult::Replaced(*v)
                            }
                            _ => {}
                        }
                    }
                    ParsedValue::Empty => {
                        // found the key with empty value, shall do nothing and continue probing
                    },
                    ParsedValue::Sentinel => return ModResult::Sentinel // should not reachable for insertion happens on new list
                }

            } else if k == EMPTY_KEY {
                let put_in_empty = |value| {
                    // found empty slot, try to CAS key and value
                    if self.cas_value(addr, 0, value) {
                        // CAS value succeed, shall store key
                        unsafe { intrinsics::atomic_store_relaxed(addr as *mut usize, key) }
                        self.occupation.fetch_add(1, Relaxed);
                        match replaced {
                            Some(v) => ModResult::Replaced(v),
                            None => ModResult::Done
                        }
                    } else {
                        // CAS failed, this entry have been taken, reprobe
                        ModResult::Fail(0)
                    }
                };
                let mod_res = match op {
                    ModOp::Insert(val) => put_in_empty(val),
                    ModOp::Sentinel => put_in_empty(SENTINEL_VALUE),
                    _ => unreachable!()
                };
                match &mod_res {
                    ModResult::Fail(_) => {},
                    _ => return mod_res
                }
            }
            idx += 1; // reprobe
            count += 1;
        }
        match op {
            ModOp::Insert(_) => panic!("Table is full, cannot insert into"),
            _ => return ModResult::NotFound
        }
    }

    #[inline(always)]
    fn get_key(&self, entry_addr: usize) -> usize {
        unsafe { intrinsics::atomic_load_relaxed(entry_addr as *mut usize) }
    }

    #[inline(always)]
    fn get_value(&self, entry_addr: usize) -> Value {
        let addr = entry_addr + mem::size_of::<usize>();
        let val = unsafe { intrinsics::atomic_load_relaxed(addr as *mut usize) };
        Value::new(val, self)
    }

    #[inline(always)]
    fn set_tombstone(&self, entry_addr: usize, original: usize) -> bool {
        self.cas_value(entry_addr, original, 0)
    }
    #[inline(always)]
    fn set_sentinel(&self, entry_addr: usize) {
        let addr = entry_addr + mem::size_of::<usize>();
        unsafe { intrinsics::atomic_store_relaxed(addr as *mut usize, SENTINEL_VALUE) }
    }
    #[inline(always)]
    fn cas_value(&self, entry_addr: usize, original: usize, value: usize) -> bool {
        let addr = entry_addr + mem::size_of::<usize>();
        unsafe { intrinsics::atomic_cxchg_relaxed(addr as *mut usize, original, value).0 == original }
    }
}

impl Value {
    pub fn new(val: usize, table: &Table) -> Self {
        let res = {
            if val == 0 {
                ParsedValue::Empty
            } else {
                let actual_val = val & table.val_bit_mask;
                let flag = val & table.inv_bit_mask;
                if flag == 1 {
                    ParsedValue::Prime(actual_val)
                } else if actual_val == 1 {
                    ParsedValue::Sentinel
                } else {
                    ParsedValue::Val(actual_val)
                }
            }
        };
        Value {
            raw: val,
            parsed: res
        }
    }
}

fn is_power_of_2(num: usize) -> bool {
    if num < 1 {return false}
    if num <= 2 {return true}
    if num % 2 == 1 {return false};
    return is_power_of_2(num / 2);
}

#[cfg(test)]
mod tests {

}