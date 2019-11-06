#![feature(allocator_api)]
#![feature(core_intrinsics)]
extern crate alloc;
#[macro_use]
extern crate log;
// usize to usize lock-free, wait free table
use alloc::alloc::Global;
use alloc::string::String;
use core::alloc::{Alloc, Layout, GlobalAlloc};
use core::cmp::Ordering;
use core::iter::Copied;
use core::marker::PhantomData;
use core::ops::Deref;
use core::ptr::NonNull;
use core::sync::atomic::Ordering::{Acquire, Relaxed, Release, SeqCst};
use core::sync::atomic::{fence, AtomicBool, AtomicPtr, AtomicUsize};
use core::{intrinsics, mem, ptr};
use std::ptr::{drop_in_place, null, null_mut};
use ModOp::Empty;

pub type EntryTemplate = (usize, usize);

const EMPTY_KEY: usize = 0;
const EMPTY_VALUE: usize = 0;
const SENTINEL_VALUE: usize = 1;

struct Value {
    raw: usize,
    parsed: ParsedValue,
}

enum ParsedValue {
    Val(usize),
    Prime(usize),
    Sentinel,
    Empty,
}

#[derive(Debug)]
enum ModResult {
    Replaced(usize),
    Fail(usize),
    Sentinel,
    NotFound,
    Done(usize), // address of placement
    TableFull,
}

struct ModOutput {
    result: ModResult,
    index: usize,
}

#[derive(Debug)]
enum ModOp<T> {
    Insert(usize, T),
    AttemptInsert(usize, T),
    Sentinel,
    Empty,
}

pub struct Chunk<V, A: Attachment<V>, ALLOC: Alloc + Default> {
    capacity: usize,
    base: usize,
    // floating-point multiplication is slow, cache this value and recompute every time when resize
    occu_limit: usize,
    occupation: AtomicUsize,
    refs: AtomicUsize,
    attachment: A,
    shadow: PhantomData<(V, ALLOC)>,
}

pub struct ChunkRef<V, A: Attachment<V>, ALLOC: Alloc + Default> {
    ptr: *mut Chunk<V, A, ALLOC>,
}

pub struct Table<V, A: Attachment<V>, ALLOC: Alloc + Default> {
    old_chunk: AtomicPtr<Chunk<V, A, ALLOC>>,
    new_chunk: AtomicPtr<Chunk<V, A, ALLOC>>,
    val_bit_mask: usize, // 0111111..
    inv_bit_mask: usize, // 1000000..
}

impl<V: Clone, A: Attachment<V>, ALLOC: Alloc + Default> Table<V, A, ALLOC> {
    pub fn with_capacity(cap: usize) -> Self {
        if !is_power_of_2(cap) {
            panic!("capacity is not power of 2");
        }
        // Each entry key value pair is 2 words
        // steal 1 bit in the MSB of value indicate Prime(1)
        let val_bit_mask = !0 << 1 >> 1;
        let chunk = Chunk::alloc_chunk(cap);
        Self {
            old_chunk: AtomicPtr::new(chunk),
            new_chunk: AtomicPtr::new(chunk),
            val_bit_mask,
            inv_bit_mask: !val_bit_mask,
        }
    }

    pub fn new() -> Self {
        Self::with_capacity(64)
    }

    pub fn get(&self, key: usize, read_attachment: bool) -> Option<(usize, Option<V>)> {
        let mut chunk = unsafe { Chunk::borrow(self.old_chunk.load(SeqCst)) };
        loop {
            let (val, idx) = self.get_from_chunk(&*chunk, key);
            match val.parsed {
                ParsedValue::Prime(val) | ParsedValue::Val(val) => {
                    return Some((
                        val,
                        if read_attachment {
                            Some(chunk.attachment.get(idx, key))
                        } else {
                            None
                        },
                    ))
                }
                ParsedValue::Sentinel => {
                    let old_chunk_base = chunk.base;
                    chunk = unsafe { Chunk::borrow(self.new_chunk.load(SeqCst)) };
                }
                ParsedValue::Empty => return None,
            }
        }
    }

    pub fn insert(&self, key: usize, value: usize, attached_val: V) -> Option<(usize)> {
        debug!("Inserting key: {}, value: {}", key, value);
        let result = self.ensure_write_new(|new_chunk_ptr| {
            let old_chunk_ptr = self.old_chunk.load(Relaxed);
            let copying = new_chunk_ptr != old_chunk_ptr;
            let old_chunk = unsafe { Chunk::borrow(old_chunk_ptr) };
            if !copying && self.check_resize(&old_chunk) {
                debug!("Resized, retry insertion key: {}, value {}", key, value);
                return Err(self.insert(key, value, attached_val.clone()));
            }
            let new_chunk = unsafe { Chunk::borrow(new_chunk_ptr) };
            let value_insertion = self.modify_entry(
                &*new_chunk,
                key,
                ModOp::Insert(value & self.val_bit_mask, attached_val.clone()),
            );
            let insertion_index = value_insertion.index;
            let mut result = None;
            match value_insertion.result {
                ModResult::Done(_) => {}
                ModResult::Replaced(v) | ModResult::Fail(v) => result = Some(v),
                ModResult::TableFull => {
                    panic!("Insertion is too fast, copying {}, cap {}, count {}, dump: {}",
                           copying, new_chunk.capacity, new_chunk.occupation.load(Relaxed),
                           self.dump(new_chunk.base, new_chunk.capacity));
                }
                ModResult::Sentinel => {
                    debug!("Insert new and see sentinel, abort");
                    return Ok(None);
                }
                _ => unreachable!("{:?}, copying: {}", value_insertion.result, copying),
            }
            if copying {
                debug_assert_ne!(new_chunk_ptr, old_chunk_ptr);
                fence(SeqCst);
                self.modify_entry(&*old_chunk, key, ModOp::Sentinel);
            }
            new_chunk.occupation.fetch_add(1, Relaxed);
            Ok(result)
        });
        result
    }

    pub fn remove(&self, key: usize) -> Option<(usize, V)> {
        self.ensure_write_new(|new_chunk_ptr| {
            let old_chunk_ptr = self.old_chunk.load(Relaxed);
            let copying = new_chunk_ptr != old_chunk_ptr;
            let new_chunk = unsafe { Chunk::borrow(new_chunk_ptr) };
            let old_chunk = unsafe { Chunk::borrow_if_cond(old_chunk_ptr, copying) };
            let mut res = self.modify_entry(&*new_chunk, key, ModOp::Empty);
            let mut retr = None;
            match res.result {
                ModResult::Done(v) | ModResult::Replaced(v) => {
                    if copying {
                        retr = Some((v, new_chunk.attachment.get(res.index, key)));
                        debug_assert_ne!(new_chunk_ptr, old_chunk_ptr);
                        fence(SeqCst);
                        self.modify_entry(&*old_chunk, key, ModOp::Sentinel);
                    }
                }
                ModResult::NotFound => {
                    let remove_from_old = self.modify_entry(&*old_chunk, key, ModOp::Empty);
                    match remove_from_old.result {
                        ModResult::Done(v) | ModResult::Replaced(v) => {
                            retr = Some((v, new_chunk.attachment.get(res.index, key)));
                        }
                        _ => {}
                    }
                    res = remove_from_old;
                }
                ModResult::TableFull => panic!("need to handle TableFull by remove"),
                _ => {}
            };
            Ok(retr)
        })
    }

    fn ensure_write_new<R, F>(&self, f: F) -> R
    where
        F: Fn(*mut Chunk<V, A, ALLOC>) -> Result<R, R>,
    {
        loop {
            let new_chunk_ptr = self.new_chunk.load(SeqCst);
            let f_res = f(new_chunk_ptr);
            match f_res {
                Ok(r) if self.new_chunk.load(SeqCst) == new_chunk_ptr => return r,
                Err(r) => return r,
                _ => {
                    debug!("Invalid write new, retry");
                }
            }
        }
    }

    fn get_from_chunk(&self, chunk: &Chunk<V, A, ALLOC>, key: usize) -> (Value, usize) {
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
                    ParsedValue::Empty => {}
                    _ => return (val_res, idx),
                }
            }
            if k == EMPTY_KEY {
                return (Value::new(0, self), 0);
            }
            idx += 1; // reprobe
            counter += 1;
        }

        // not found
        return (Value::new(0, self), 0);
    }

    fn modify_entry(&self, chunk: &Chunk<V, A, ALLOC>, key: usize, op: ModOp<V>) -> ModOutput {
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
                                chunk.attachment.erase(idx, key);
                                return ModOutput::new(ModResult::Done(addr), idx);
                            }
                            ModOp::Empty | ModOp::Insert(_, _) => {
                                if !self.set_tombstone(addr, val.raw) {
                                    // this insertion have conflict with others
                                    // other thread changed the value
                                    // should fail (?)
                                    return ModOutput::new(ModResult::Fail(*v), idx);
                                } else {
                                    // we have put tombstone on the value
                                    chunk.attachment.erase(idx, key);
                                    replaced = Some(*v);
                                }
                            }
                            ModOp::AttemptInsert(_, _) => {
                                // Attempting insert existed entry, skip
                                return ModOutput::new(ModResult::Fail(*v), idx);
                            }
                        }
                        match op {
                            ModOp::Empty => return ModOutput::new(ModResult::Replaced(*v), idx),
                            _ => {}
                        }
                    }
                    ParsedValue::Empty => {
                        // found the key with empty value, shall do nothing and continue probing
                    }
                    ParsedValue::Sentinel => return ModOutput::new(ModResult::Sentinel, idx), // should not reachable for insertion happens on new list
                }
            } else if k == EMPTY_KEY {
                // Probing empty entry
                let put_in_empty = |value, attach_val| {
                    // found empty slot, try to CAS key and value
                    if self.cas_value(addr, 0, value) {
                        // CAS value succeed, shall store key
                        if let Some(attach_val) = attach_val {
                            chunk.attachment.set(idx, k, attach_val);
                        }
                        unsafe { intrinsics::atomic_store_relaxed(addr as *mut usize, key) }
                        match replaced {
                            Some(v) => ModResult::Replaced(v),
                            None => ModResult::Done(addr),
                        }
                    } else {
                        // CAS failed, this entry have been taken, reprobe
                        ModResult::Fail(0)
                    }
                };
                let mod_res = match op {
                    ModOp::Insert(val, ref attach_val)
                    | ModOp::AttemptInsert(val, ref attach_val) => {
                        debug!(
                            "Inserting entry key: {}, value: {}, raw: {:b}, addr: {}",
                            key,
                            val & self.val_bit_mask,
                            val,
                            addr
                        );
                        put_in_empty(val, Some(attach_val.clone()))
                    }
                    ModOp::Sentinel => put_in_empty(SENTINEL_VALUE, None),
                    ModOp::Empty => return ModOutput::new(ModResult::Fail(0), idx),
                    _ => unreachable!(),
                };
                match &mod_res {
                    ModResult::Fail(_) => {}
                    _ => return ModOutput::new(mod_res, idx),
                }
            }
            idx += 1; // reprobe
            count += 1;
        }
        match op {
            ModOp::Insert(_, _) | ModOp::AttemptInsert(_, _) => {
                ModOutput::new(ModResult::TableFull, 0)
            }
            _ => ModOutput::new(ModResult::NotFound, 0),
        }
    }

    fn all_from_chunk(&self, chunk: &Chunk<V, A, ALLOC>) -> Vec<(usize, usize, V)> {
        let mut idx = 0;
        let entry_size = mem::size_of::<EntryTemplate>();
        let cap = chunk.capacity;
        let base = chunk.base;
        let mut counter = 0;
        let mut res = vec![];
        while counter < cap {
            idx &= (cap - 1);
            let addr = base + idx * entry_size;
            let k = self.get_key(addr);
            if k != EMPTY_KEY {
                let val_res = self.get_value(addr);
                match val_res.parsed {
                    ParsedValue::Val(v) | ParsedValue::Prime(v) => {
                        res.push((k, v, chunk.attachment.get(idx, k)))
                    }
                    _ => {}
                }
            }
            idx += 1; // reprobe
            counter += 1;
        }
        return res;
    }

    fn entries(&self) -> Vec<(usize, usize, V)> {
        let old_chunk_ptr = self.old_chunk.load(Relaxed);
        let new_chunk_ptr = self.new_chunk.load(Relaxed);
        let old_chunk = unsafe { Chunk::borrow(old_chunk_ptr) };
        let new_chunk = unsafe { Chunk::borrow(new_chunk_ptr) };
        let mut res = self.all_from_chunk(&*old_chunk);
        if old_chunk_ptr != new_chunk_ptr {
            res.append(&mut self.all_from_chunk(&*new_chunk));
        }
        return res;
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
        unsafe {
            intrinsics::atomic_cxchg_relaxed(addr as *mut usize, original, value).0 == original
        }
    }

    #[inline(always)]
    fn check_resize(&self, old_chunk_ref: &ChunkRef<V, A, ALLOC>) -> bool {
        let old_chunk_ptr = old_chunk_ref.ptr;
        let occupation = old_chunk_ref.occupation.load(Relaxed);
        let occu_limit = old_chunk_ref.occu_limit;
        if occupation <= occu_limit {
            return false;
        }
        // resize
        debug!("Resizing");
        let old_cap = old_chunk_ref.capacity;
        let mult = if old_cap < 2048 { 4 } else { 1 };
        let new_cap = old_cap << mult;
        let new_chunk_ptr = Chunk::alloc_chunk(new_cap);
        if self
            .new_chunk
            .compare_and_swap(old_chunk_ptr, new_chunk_ptr, SeqCst)
            != old_chunk_ptr
        {
            // other thread have allocated new chunk and wins the competition, exit
            unsafe {
                Chunk::mark_garbage(new_chunk_ptr);
            }
            return true;
        }
        let new_chunk_ins = unsafe { Chunk::borrow(new_chunk_ptr) };
        let new_base = new_chunk_ins.base;
        let mut old_address = old_chunk_ref.base as usize;
        let boundary = old_address + chunk_size_of(old_cap);
        let mut effective_copy = 0;
        let mut idx = 0;
        while old_address < boundary {
            // iterate the old chunk to extract entries that is NOT empty
            let key = self.get_key(old_address);
            let value = self.get_value(old_address);
            if key != EMPTY_KEY
            // Empty entry, skip
            {
                // Reasoning value states
                match &value.parsed {
                    ParsedValue::Val(v) => {
                        // Insert entry into new chunk, in case of failure, skip this entry
                        // Value should be primed
                        debug!("Moving key: {}, value: {}", key, v);
                        let primed_val = value.raw | self.inv_bit_mask;
                        let attached_val = old_chunk_ref.attachment.get(idx, key);
                        let new_chunk_insertion = self.modify_entry(
                            &*new_chunk_ins,
                            key,
                            ModOp::AttemptInsert(primed_val, attached_val),
                        );
                        let inserted_addr = match new_chunk_insertion.result {
                            ModResult::Done(addr) => Some(addr), // continue procedure
                            ModResult::Fail(v) => None,
                            ModResult::Replaced(_) => {
                                unreachable!("Attempt insert does not replace anything");
                            }
                            ModResult::Sentinel => {
                                unreachable!("New chunk should not have sentinel");
                            }
                            ModResult::NotFound => unreachable!(),
                            ModResult::TableFull => panic!(),
                        };
                        if let Some(entry_addr) = inserted_addr {
                            fence(SeqCst);
                            // cas to ensure sentinel into old chunk
                            if self.cas_value(old_address, value.raw, SENTINEL_VALUE) {
                                // strip prime
                                let stripped = primed_val & self.val_bit_mask;
                                debug_assert_ne!(stripped, SENTINEL_VALUE);
                                if self.cas_value(entry_addr, primed_val, stripped) {
                                    debug!(
                                        "Effective copy key: {}, value {}, addr: {}",
                                        key, stripped, entry_addr
                                    );
                                    old_chunk_ref.attachment.erase(idx, key);
                                    effective_copy += 1;
                                }
                            } else {
                                continue; // retry this entry
                            }
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
            idx += 1;
        }
        // resize finished, make changes on the numbers
        new_chunk_ins.occupation.fetch_add(effective_copy, Relaxed);
        debug_assert_ne!(old_chunk_ptr as usize, new_base);
        if self
            .old_chunk
            .compare_and_swap(old_chunk_ptr, new_chunk_ptr, SeqCst)
            != old_chunk_ptr
        {
            panic!();
        }
        debug!("{}", self.dump(new_base, new_cap));
        unsafe {
            Chunk::mark_garbage(old_chunk_ptr);
        }
        return true;
    }

    fn dump(&self, base: usize, cap: usize) -> &str {
        for i in 0..cap {
            let addr = base + i * entry_size();
            debug!("{}-{}\t", self.get_key(addr), self.get_value(addr).raw);
            if i % 8 == 0 {
                debug!("")
            }
        }
        "DUMPED"
    }
}

impl<V, A: Attachment<V>, ALLOC: Alloc + Default> Drop for Table<V, A, ALLOC> {
    fn drop(&mut self) {
        let old_chunk = self.old_chunk.load(Relaxed);
        let new_chunk = self.new_chunk.load(Relaxed);
        unsafe {
            if old_chunk != null_mut() {
                Chunk::mark_garbage(old_chunk);
            }
            if old_chunk != new_chunk  && new_chunk != null_mut() {
                Chunk::mark_garbage(new_chunk);
            }
        }
    }
}

impl Value {
    pub fn new<V, A: Attachment<V>, ALLOC: Alloc + Default>(val: usize, table: &Table<V, A, ALLOC>) -> Self {
        let res = {
            if val == 0 {
                ParsedValue::Empty
            } else {
                let actual_val = val & table.val_bit_mask;
                let flag = val & table.inv_bit_mask;
                if flag != 0 {
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
            parsed: res,
        }
    }
}

impl ParsedValue {
    fn unwrap(&self) -> usize {
        match self {
            ParsedValue::Val(v) | ParsedValue::Val(v) => *v,
            _ => panic!(),
        }
    }
}

impl<V, A: Attachment<V>, ALLOC: Alloc + Default> Chunk<V, A, ALLOC> {
    fn alloc_chunk(capacity: usize) -> *mut Self {
        let base = alloc_mem::<ALLOC>(chunk_size_of(capacity));
        let ptr = alloc_mem::<ALLOC>(mem::size_of::<Self>()) as *mut Self;
        unsafe {
            ptr::write(
                ptr,
                Self {
                    base,
                    capacity,
                    occupation: AtomicUsize::new(0),
                    occu_limit: occupation_limit(capacity),
                    refs: AtomicUsize::new(1),
                    attachment: A::new(capacity),
                    shadow: PhantomData,
                },
            )
        };
        ptr
    }
    unsafe fn borrow(ptr: *mut Chunk<V, A, ALLOC>) -> ChunkRef<V, A, ALLOC> {
        let chunk = &*ptr;
        chunk.refs.fetch_add(1, Relaxed);
        ChunkRef { ptr: ptr }
    }

    unsafe fn borrow_if_cond(ptr: *mut Chunk<V, A, ALLOC>, cond: bool) -> ChunkRef<V, A, ALLOC> {
        if cond {
            unsafe { Chunk::borrow(ptr) }
        } else {
            ChunkRef::null_ref()
        }
    }

    unsafe fn mark_garbage(ptr: *mut Chunk<V, A, ALLOC>) {
        // Caller promise this chunk will not be reachable from the outside except snapshot in threads
        {
            let chunk = &*ptr;
            chunk.refs.fetch_sub(1, Relaxed);
        }
        Self::check_gc(ptr);
    }
    unsafe fn check_gc(ptr: *mut Chunk<V, A, ALLOC>) {
        let chunk = &*ptr;
        if chunk.refs.load(Relaxed) == 0 && chunk.refs.compare_and_swap(0, core::usize::MAX, Relaxed) == 0 {
            chunk.attachment.dealloc();
            dealloc_mem::<ALLOC>(ptr as usize, mem::size_of::<Self>());
            dealloc_mem::<ALLOC>(chunk.base, chunk_size_of(chunk.capacity));
        }
    }
}

impl ModOutput {
    pub fn new(res: ModResult, idx: usize) -> Self {
        Self {
            result: res,
            index: idx,
        }
    }
}

impl<V, A: Attachment<V>, ALLOC: Alloc + Default> Drop for ChunkRef<V, A, ALLOC> {
    fn drop(&mut self) {
        {
            if self.ptr as usize == 0 {
                return;
            }
            let chunk = unsafe { &*self.ptr };
            chunk.refs.fetch_sub(1, Relaxed);
        }
        unsafe { Chunk::check_gc(self.ptr) }
    }
}

impl<V, A: Attachment<V>, ALLOC: Alloc + Default> Deref for ChunkRef<V, A, ALLOC> {
    type Target = Chunk<V, A, ALLOC>;

    fn deref(&self) -> &Self::Target {
        debug_assert_ne!(self.ptr as usize, 0);
        unsafe { &*self.ptr }
    }
}

impl<V, A: Attachment<V>, ALLOC: Alloc + Default> ChunkRef<V, A, ALLOC> {
    fn null_ref() -> Self {
        Self {
            ptr: 0 as *mut Chunk<V, A, ALLOC>,
        }
    }
}

fn is_power_of_2(x: usize) -> bool {
    (x != 0) && ((x & (x - 1)) == 0)
}

#[inline(always)]
fn occupation_limit(cap: usize) -> usize {
    (cap as f64 * 0.7f64) as usize
}

#[inline(always)]
fn entry_size() -> usize {
    mem::size_of::<EntryTemplate>()
}

#[inline(always)]
fn chunk_size_of(cap: usize) -> usize {
    cap * entry_size()
}

pub trait Attachment<V> {
    fn new(cap: usize) -> Self;
    fn get(&self, index: usize, key: usize) -> V;
    fn set(&self, index: usize, key: usize, att_value: V);
    fn erase(&self, index: usize, key: usize);
    fn dealloc(&self);
}

pub struct WordAttachment;

// this attachment basically do nothing and sized zero
impl Attachment<()> for WordAttachment {
    fn new(cap: usize) -> Self {
        Self
    }

    fn get(&self, index: usize, key: usize) -> () {}

    fn set(&self, index: usize, key: usize, att_value: ()) {}

    fn erase(&self, index: usize, key: usize) {}

    fn dealloc(&self) {}
}

pub type WordTable<ALLOC: Alloc + Default> = Table<(), WordAttachment, ALLOC>;

pub struct ObjectAttachment<T, A: Alloc + Default> {
    obj_chunk: usize,
    size: usize,
    obj_size: usize,
    shadow: PhantomData<(T, A)>,
}

impl<T: Clone, A: Alloc + Default> Attachment<T> for ObjectAttachment<T, A> {
    fn new(cap: usize) -> Self {
        let obj_size = mem::size_of::<T>();
        let obj_chunk_size = cap * obj_size;
        let addr = alloc_mem::<A>(obj_chunk_size);
        Self {
            obj_chunk: addr,
            size: obj_chunk_size,
            obj_size,
            shadow: PhantomData,
        }
    }

    fn get(&self, index: usize, key: usize) -> T {
        let addr = self.addr_by_index(index);
        unsafe { (*(addr as *mut T)).clone() }
    }

    fn set(&self, index: usize, key: usize, att_value: T) {
        let addr = self.addr_by_index(index);
        unsafe { ptr::write(addr as *mut T, att_value) }
    }

    fn erase(&self, index: usize, key: usize) {
        unsafe { drop(self.addr_by_index(index) as *mut T) }
    }

    fn dealloc(&self) {
        dealloc_mem::<A>(self.obj_chunk, self.size);
    }
}

impl<T, A: Alloc + Default> ObjectAttachment<T, A> {
    fn addr_by_index(&self, index: usize) -> usize {
        self.obj_chunk + index * self.obj_size
    }
}

pub trait Map<K, V> {
    fn with_capacity(cap: usize) -> Self;
    fn get(&self, key: K) -> Option<V>;
    fn insert(&self, key: K, value: V) -> Option<()>;
    fn remove(&self, key: K) -> Option<V>;
    fn entries(&self) -> Vec<(usize, V)>;
    fn contains(&self, key: K) -> bool;
}

const NUM_KEY_FIX: usize = 5;

pub struct ObjectMap<V: Clone, ALLOC: Alloc + Default = Global> {
    table: Table<V, ObjectAttachment<V, ALLOC>, ALLOC>,
}

impl<V: Clone> Map<usize, V> for ObjectMap<V> {
    fn with_capacity(cap: usize) -> Self {
        Self {
            table: Table::with_capacity(cap),
        }
    }

    fn get(&self, key: usize) -> Option<V> {
        self.table.get(key + NUM_KEY_FIX, true).map(|v| v.1.unwrap())
    }

    fn insert(&self, key: usize, value: V) -> Option<()> {
        self.table.insert(key + NUM_KEY_FIX, !0, value).map(|_| ())
    }

    fn remove(&self, key: usize) -> Option<V> {
        self.table.remove(key + NUM_KEY_FIX).map(|(_, v)| v)
    }

    fn entries(&self) -> Vec<(usize, V)> {
        self.table
            .entries()
            .into_iter()
            .map(|(k, _, v)| (k - NUM_KEY_FIX, v))
            .collect()
    }

    fn contains(&self, key: usize) -> bool {
        self.table.get(key + NUM_KEY_FIX, false).is_some()
    }
}

pub struct WordMap<ALLOC: Alloc + Default = Global> {
    table: WordTable<ALLOC>,
}

impl Map<usize, usize> for WordMap {
    fn with_capacity(cap: usize) -> Self {
        Self {
            table: Table::with_capacity(cap),
        }
    }

    fn get(&self, key: usize) -> Option<usize> {
        self.table.get(key + NUM_KEY_FIX, false).map(|v| v.0)
    }

    fn insert(&self, key: usize, value: usize) -> Option<()> {
        self.table.insert(key + NUM_KEY_FIX, value, ()).map(|_| ())
    }

    fn remove(&self, key: usize) -> Option<usize> {
        self.table.remove(key + NUM_KEY_FIX).map(|(v, _)| v)
    }
    fn entries(&self) -> Vec<(usize, usize)> {
        self.table
            .entries()
            .into_iter()
            .map(|(k, v, _)| (k - NUM_KEY_FIX, v))
            .collect()
    }

    fn contains(&self, key: usize) -> bool {
        self.get(key).is_some()
    }
}

#[inline(always)]
fn alloc_mem<A: Alloc + Default>(size: usize) -> usize {
    let align = mem::align_of::<EntryTemplate>();
    let layout = Layout::from_size_align(size, align).unwrap();
    let mut alloc = A::default();
    // must be all zeroed
    unsafe { alloc.alloc_zeroed(layout) }.unwrap().as_ptr() as usize
}

#[inline(always)]
fn dealloc_mem<A: Alloc + Default + Default>(ptr: usize, size: usize) {
    let align = mem::align_of::<EntryTemplate>();
    let layout = Layout::from_size_align(size, align).unwrap();
    let mut alloc = A::default();
    unsafe { alloc.dealloc(NonNull::<u8>::new(ptr as *mut u8).unwrap(), layout) }
}
