#![no_std]
#![feature(allocator_api)]
#![feature(core_intrinsics)]
extern crate alloc;
#[macro_use]
extern crate log;
// usize to usize lock-free, wait free table

use alloc::alloc::Global;
use core::alloc::{Alloc, Layout};
use core::{mem, ptr, intrinsics};
use core::sync::atomic::{AtomicUsize, AtomicPtr, fence, AtomicBool};
use core::sync::atomic::Ordering::{Relaxed, Acquire, Release};
use core::iter::Copied;
use core::cmp::Ordering;
use core::ptr::NonNull;
use ModOp::Empty;
use alloc::string::String;
use core::ops::Deref;

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

#[derive(Debug)]
enum ModResult {
    Replaced(usize),
    Fail(usize),
    Sentinel,
    NotFound,
    Done(usize) // address of placement
}

enum ModOp {
    Insert(usize),
    AttemptInsert(usize),
    Sentinel,
    Empty
}

pub struct Chunk {
    capacity: usize,
    base: usize,
    referenced: AtomicUsize,
    is_garbage: AtomicBool
}

pub struct ChunkRef {
    chunk: *mut Chunk
}

pub struct Table {
    chunk: AtomicPtr<Chunk>,
    new_chunk: AtomicPtr<Chunk>,
    occupation: AtomicUsize,
    // floating-point multiplication is slow, cache this value and recompute every time when resize
    occu_limit: AtomicUsize,
    val_bit_mask: usize, // 0111111..
    inv_bit_mask: usize  // 1000000..
}

impl Table {
    pub fn with_capacity(cap: usize) -> Self {
        if !is_power_of_2(cap) {
            panic!("capacity is not power of 2");
        }
        // Each entry key value pair is 2 words
        // steal 1 bit in the MSB of value indicate Prime(1)
        let val_bit_mask = !0 << 1 >> 1;
        let chunk = Chunk::alloc_chunk(cap);
        Self {
            chunk: AtomicPtr::new(chunk),
            new_chunk: AtomicPtr::new(chunk),
            occupation: AtomicUsize::new(0),
            occu_limit: AtomicUsize::new(occupation_limit(cap)),
            val_bit_mask,
            inv_bit_mask: !val_bit_mask
        }
    }

    pub fn new() -> Self {
        Self::with_capacity(64)
    }

    pub fn get(&self, key: usize) -> Option<usize> {
        let mut chunk = unsafe { Chunk::borrow(self.chunk.load(Relaxed)) };
        loop {
            let val = self.get_from_chunk(&*chunk, key);
            match val.parsed {
                ParsedValue::Prime(val) | ParsedValue::Val(val) => return Some(val),
                ParsedValue::Sentinel => {
                    let old_chunk_base = chunk.base;
                    chunk = unsafe { Chunk::borrow(self.new_chunk.load(Relaxed)) };
                    debug_assert_ne!(old_chunk_base, chunk.base);
                }
                ParsedValue::Empty => return None
            }
        }
    }

    pub fn insert(&self, key: usize, value: usize) -> Option<usize> {
        debug!("Inserting key: {}, value: {}", key, value);
        let new_chunk_ptr = self.new_chunk.load(Relaxed);
        let old_chunk_ptr = self.chunk.load(Relaxed);
        let copying = new_chunk_ptr != old_chunk_ptr;
        if !copying && self.check_resize(old_chunk_ptr) {
            debug!("Resized, retry insertion key: {}, value {}", key, value);
            return self.insert(key, value)
        }
        let new_chunk = unsafe { Chunk::borrow(new_chunk_ptr) };
        let value_insertion = self.modify_entry(&*new_chunk, key, ModOp::Insert(value));
        let mut result = None;
        match value_insertion {
            ModResult::Done(_) => {},
            ModResult::Replaced(v) | ModResult::Fail(v) => {
                result = Some(v)
            }
            _ => unreachable!("{:?}, copying: {}", value_insertion, copying)
        };
        if copying {
            fence(Acquire);
            let old_chunk = unsafe { Chunk::borrow(old_chunk_ptr) };
            self.modify_entry(&*old_chunk, key, ModOp::Sentinel);
            fence(Release);
        }
        self.occupation.fetch_add(1, Relaxed);
        result
    }

    pub fn remove(&self, key: usize) -> Option<usize> {
        let new_chunk_ptr = self.new_chunk.load(Relaxed);
        let old_chunk_ptr = self.chunk.load(Relaxed);
        let copying = new_chunk_ptr != old_chunk_ptr;
        let new_chunk = unsafe { Chunk::borrow(new_chunk_ptr) };
        let res = self.modify_entry(&*new_chunk, key, ModOp::Empty);
        match res {
            ModResult::Done(_) | ModResult::Replaced(_) | ModResult::NotFound => if copying {
                let old_chunk = unsafe { Chunk::borrow(old_chunk_ptr) };
                self.modify_entry(&*old_chunk, key, ModOp::Sentinel);
            }
            _ => {}
        }
        match res {
            ModResult::Replaced(v) => Some(v),
            _ => None
        }
    }

    fn get_from_chunk(&self, chunk: &Chunk, key: usize) -> Value {
        let mut idx = key;
        let entry_size = mem::size_of::<EntryTemplate>();
        let cap = chunk.capacity;
        let base = chunk.base;
        let mut counter = 0;
        while counter < cap {
            idx &= (cap - 1);
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

    fn modify_entry(&self, chunk: &Chunk, key: usize, op: ModOp) -> ModResult {
        let cap = chunk.capacity;
        let base = chunk.base;
        let mut idx = key;
        let entry_size = mem::size_of::<EntryTemplate>();
        let mut replaced = None;
        let mut count = 0;
        while count <= cap {
            idx &= (cap - 1);
            let addr = base + idx * entry_size;
            let k = self.get_key(addr);
            if k == key {
                // Probing non-empty entry
                let val = self.get_value(addr);
                match &val.parsed {
                    ParsedValue::Val(v) | ParsedValue::Prime(v) => {
                        match op {
                            ModOp::Sentinel => {
                                self.set_sentinel(addr);
                                return ModResult::Done(addr);
                            }
                            ModOp::Empty | ModOp::Insert(_) => {
                                if !self.set_tombstone(addr, val.raw) {
                                    // this insertion have conflict with others
                                    // other thread changed the value
                                    // should fail (?)
                                    return ModResult::Fail(*v);
                                } else {
                                    // we have put tombstone on the value
                                    replaced = Some(*v);
                                }
                            }
                            ModOp::AttemptInsert(_) => {
                                // Attempting insert existed entry, skip
                                return ModResult::Fail(*v);
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
                // Probing empty entry
                let put_in_empty = |value| {
                    // found empty slot, try to CAS key and value
                    if self.cas_value(addr, 0, value) {
                        // CAS value succeed, shall store key
                        unsafe { intrinsics::atomic_store_relaxed(addr as *mut usize, key) }
                        match replaced {
                            Some(v) => ModResult::Replaced(v),
                            None => ModResult::Done(addr)
                        }
                    } else {
                        // CAS failed, this entry have been taken, reprobe
                        ModResult::Fail(0)
                    }
                };
                let mod_res = match op {
                    ModOp::Insert(val) | ModOp::AttemptInsert(val) => {
                        debug!("Inserting entry key: {}, value: {}, raw: {:b}, addr: {}",
                               key, val & self.val_bit_mask, val, addr);
                        put_in_empty(val)
                    },
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

    #[inline(always)]
    fn check_resize(&self, old_chunk_ptr: *mut Chunk) -> bool {
        let occupation = self.occupation.load(Relaxed);
        let occu_limit = self.occu_limit.load(Relaxed);
        if occupation > occu_limit {
            // resize
            debug!("Resizing");
            let old_chunk_ins = unsafe { Chunk::borrow(old_chunk_ptr) };
            let new_cap = old_chunk_ins.capacity << 1;
            let new_chunk_ptr = Chunk::alloc_chunk(new_cap);
            if self.new_chunk.compare_and_swap(old_chunk_ptr, new_chunk_ptr, Relaxed) != old_chunk_ptr {
                // other thread have allocated new chunk and wins the competition, exit
                unsafe { Chunk::mark_garbage(new_chunk_ptr); }
                return true;
            }
            self.occu_limit.store(occupation_limit(new_cap), Relaxed);
            let new_chunk_ins = unsafe { Chunk::borrow(new_chunk_ptr) };
            let new_base = new_chunk_ins.base;
            let mut old_address = old_chunk_ins.base as usize;
            let boundary = old_address + chunk_size_of(old_chunk_ins.capacity);
            let mut effective_copy = 0;
            while old_address < boundary  {
                // iterate the old chunk to extract entries that is NOT empty
                let key = self.get_key(old_address);
                let value = self.get_value(old_address);
                if key != EMPTY_KEY // Empty entry, skip
                {
                    // Reasoning value states
                    match &value.parsed {
                        ParsedValue::Val(v) => {
                            // Insert entry into new chunk, in case of failure, skip this entry
                            // Value should be primed
                            debug!("Moving key: {}, value: {}", key, v);
                            let primed_val = value.raw | self.inv_bit_mask;
                            let new_chunk_insertion = self.modify_entry(
                                &*new_chunk_ins,
                                key,
                                ModOp::AttemptInsert(primed_val)
                            );
                            let inserted_addr = match new_chunk_insertion {
                                ModResult::Done(addr) => Some(addr), // continue procedure
                                ModResult::Fail(v) => None,
                                ModResult::Replaced(_) => {
                                    unreachable!("Attempt insert does not replace anything");
                                }
                                ModResult::Sentinel => {
                                    unreachable!("New chunk should not have sentinel");
                                }
                                ModResult::NotFound => {
                                    unreachable!()
                                }
                            };
                            if let Some(entry_addr) = inserted_addr {
                                fence(Acquire);
                                // cas to ensure sentinel into old chunk
                                if self.cas_value(old_address, value.raw, SENTINEL_VALUE) {
                                    // strip prime
                                    let stripped = primed_val & self.val_bit_mask;
                                    debug_assert_ne!(stripped, SENTINEL_VALUE);
                                    if self.cas_value(entry_addr, primed_val, stripped) {
                                        debug!("Effective copy key: {}, value {}, addr: {}",
                                               key, stripped, entry_addr);
                                        effective_copy += 1;
                                    }
                                } else {
                                    fence(Release);
                                    continue; // retry this entry
                                }
                                fence(Release);
                            }
                        }
                        ParsedValue::Prime(v) => {
                            // Should never have prime in old chunk
                            panic!("Prime in old chunk when resizing")
                        }
                        ParsedValue::Sentinel => {
                            // Sentinel, skip
                            // Sentinel in old chunk implies its new value have already in the new chunk
                            debug!("Skip copy sentinel");
                        }
                        ParsedValue::Empty => {
                            // Empty, skip
                            debug!("Skip copy empty, key: {}", key);
                        }
                    }
                }
                old_address += entry_size();
            }
            // resize finished, make changes on the numbers
            let changes = occupation as isize - effective_copy;
            if changes > 0 {
                self.occupation.fetch_sub(changes as usize, Relaxed);
            } else {
                self.occupation.fetch_add((-changes) as usize, Relaxed);
            }
            debug_assert_ne!(old_chunk_ptr as usize, new_base);
            if self.chunk.compare_and_swap(old_chunk_ptr, new_chunk_ptr, Relaxed) != old_chunk_ptr {
                panic!();
            }
            unsafe { Chunk::mark_garbage(old_chunk_ptr); }
            debug!("{}", self.dump(new_base, new_cap));
            return true;
        }
        false
    }

    fn dump(&self, base: usize, cap: usize) -> &str {
        for i in 0..cap {
            let addr = base + i * entry_size();
            debug!("{}-{}\t", self.get_key(addr), self.get_value(addr).raw);
            if i % 8 == 0 { debug!("") }
        }
        "DUMPED"
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

impl ParsedValue {
    fn unwrap(&self) -> usize {
        match self {
            ParsedValue::Val(v) | ParsedValue::Val(v) => *v,
            _ => panic!()
        }
    }
}

impl Chunk {
    fn alloc_chunk(capacity: usize) -> *mut Self {
        let base = alloc_mem(chunk_size_of(capacity));
        let ptr = alloc_mem(mem::size_of::<Self>()) as *mut Self;
        unsafe { ptr::write(ptr, Self {
            base, capacity,
            is_garbage: AtomicBool::new(false),
            referenced: AtomicUsize::new(0)
        }) };
        ptr
    }
    unsafe fn borrow(ptr: *mut Chunk) -> ChunkRef {
        let chunk = &*ptr;
        chunk.referenced.fetch_add(1, Relaxed);
        ChunkRef {
            chunk: ptr
        }
    }
    unsafe fn mark_garbage(ptr: *mut Chunk) {
        // Caller promise this chunk will not be reachable from the outside except snapshot in threads
        let chunk = &*ptr;
        chunk.is_garbage.store(true, Relaxed);
        Self::check_gc(ptr);
    }
    unsafe fn check_gc(ptr: *mut Chunk) {
        let chunk = &*ptr;
        if chunk.is_garbage.load(Relaxed) && chunk.referenced.load(Relaxed) == 0 {
            dealloc_mem(ptr as usize, mem::size_of::<Self>());
            dealloc_mem(chunk.base, chunk_size_of(chunk.capacity));
        }
    }
}

impl Drop for ChunkRef {
    fn drop(&mut self) {
        let chunk = unsafe { &*self.chunk };
        chunk.referenced.fetch_sub(1, Relaxed);
        unsafe { Chunk::check_gc(self.chunk) }
    }
}

impl Deref for ChunkRef {
    type Target = Chunk;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.chunk }
    }
}

fn is_power_of_2(num: usize) -> bool {
    if num < 1 {return false}
    if num <= 2 {return true}
    if num % 2 == 1 {return false};
    return is_power_of_2(num / 2);
}

#[inline(always)]
fn occupation_limit(cap: usize) -> usize {
    (cap as f64 * 0.8f64) as usize
}

#[inline(always)]
fn entry_size() -> usize {
    mem::size_of::<EntryTemplate>()
}

#[inline(always)]
fn chunk_size_of(cap: usize) -> usize {
    cap * entry_size()
}

fn alloc_mem(size: usize) -> usize {
    let align = mem::align_of::<EntryTemplate>();
    let layout = Layout::from_size_align(size, align).unwrap();
    unsafe { Global.alloc(layout) }.unwrap().as_ptr() as usize
}

fn dealloc_mem(ptr: usize, size: usize) {
    let align = mem::align_of::<EntryTemplate>();
    let layout = Layout::from_size_align(size, align).unwrap();
    unsafe { Global.dealloc(NonNull::<u8>::new(ptr as *mut u8).unwrap(), layout) }
}

#[cfg(test)]
mod tests {

}