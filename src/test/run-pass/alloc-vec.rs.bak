// Copyright 2015 The Rust Project Developers. See the COPYRIGHT file
// at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Demo first class Allocators for Vec

#![feature(alloc, allocator_api, core, heap_api, nonzero, catch_panic)]

// TODO: redo this demo in terms of e.g. scoped_threadpool on crates.io
#![feature(scoped)]

extern crate alloc;
extern crate core;


use core::nonzero::NonZero;
use std::sync::atomic::{AtomicPtr, Ordering};

use alloc::{heap, Address, Allocator, Kind};
use alloc::AllocKind as AllocKindTrait;

#[derive(Debug)]
#[allow(raw_pointer_derive)] // for Debug its okay
struct DumbBumpAlloc {
    name: &'static str,
    ptr: *mut u8,
    end: *mut u8,
    avail: AtomicPtr<u8>,
    align: usize,
}

impl DumbBumpAlloc {
    fn new(name: &'static str,
           size_in_bytes: usize,
           start_align: usize) -> DumbBumpAlloc {
        unsafe {
            let ptr = heap::allocate(size_in_bytes, start_align);
            if ptr.is_null() { panic!("allocation failed."); }
            let end = ptr.offset(size_in_bytes as isize);
            DumbBumpAlloc {
                name: name,
                ptr: ptr, end: end, avail: AtomicPtr::new(ptr),
                align: start_align
            }
        }
    }
}

impl Drop for DumbBumpAlloc {
    fn drop(&mut self) {
        unsafe {
            let size = self.end as usize - self.ptr as usize;
            heap::deallocate(self.ptr, size, self.align);
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum BumpAllocError { MemoryExhausted, Interference }

impl alloc::AllocError for BumpAllocError {
    fn invalid_input() -> Self { BumpAllocError::MemoryExhausted }
    fn is_memory_exhausted(&self) -> bool { *self == BumpAllocError::MemoryExhausted  }
    fn is_request_unsupported(&self) -> bool { false }
}

#[allow(dead_code)]
impl BumpAllocError {
    // potential API extension: use this for errors that indicate that
    // retrying the request (without freeing memory in the interim)
    // phas a chance at success.
    fn is_transient(&self) -> bool { *self == BumpAllocError::Interference }
}


impl<'a> Allocator for &'a DumbBumpAlloc {
    type Kind = alloc::Kind;
    type Error = BumpAllocError;

    unsafe fn alloc(&mut self, kind: &Self::Kind) -> Result<Address, Self::Error> {
        // println!("alloc start");
        let curr = self.avail.load(Ordering::Relaxed) as usize;
        // println!("alloc loaded");
        let align = *kind.align();
        let curr_aligned = (curr + (align - 1)) & !(align - 1);
        let size = *kind.size();
        // println!("alloc check capacity");
        let avail = (self.end as usize) - curr_aligned;
        if avail <= size {
            // println!("alloc exhausted: avail {}, size: {}", avail, size);
            return Err(BumpAllocError::MemoryExhausted);
        }

        // println!("alloc avail");

        let curr = curr as *mut u8;
        let curr_aligned = curr_aligned as *mut u8;
        let new_curr = curr_aligned.offset(size as isize);

        // println!("alloc commit");
        if curr != self.avail.compare_and_swap(curr, new_curr, Ordering::Relaxed) {
            // println!("alloc finis err");
            return Err(BumpAllocError::Interference);
        } else {
            println!("alloc finis ok: 0x{:x} size: {}", curr_aligned as usize, size);
            return Ok(NonZero::new(curr_aligned));
        }
    }

    unsafe fn dealloc(&mut self, _ptr: Address, _kind: &Self::Kind) {
        // this bump-allocator just no-op's on dealloc
    }

    unsafe fn oom(&mut self) -> ! {
        panic!("exhausted memory in {}", self.name);
    }

}

fn demo_alloc<A1:Allocator, A2:Allocator, F:Fn()>(a1:A1, a2: A2, print_state: F) {
    let mut v1 = Vec::new_in(a1);
    let mut v2 = Vec::new_in(a2);
    println!("demo_alloc, v1; {:?} v2: {:?}", v1, v2);
    for i in 0..10 {
        v1.push(i as u64 * 1000);
        v2.push(i as u8);
        v2.push(i as u8);
    }
    println!("demo_alloc, v1; {:?} v2: {:?}", v1, v2);
    print_state();
    for i in 10..100 {
        v1.push(i as u64 * 1000);
        v2.push(i as u8);
        v2.push(i as u8);
    }
    println!("demo_alloc, v1.len: {} v2.len: {}", v1.len(), v2.len());
    print_state();
    for i in 100..1000 {
        v1.push(i as u64 * 1000);
        v2.push(i as u8);
        v2.push(i as u8);
    }
    println!("demo_alloc, v1.len: {} v2.len: {}", v1.len(), v2.len());
    print_state();
}

fn main() {
    use std::thread::catch_panic;

    if let Err(panicked) = catch_panic(|| {
        let alloc = DumbBumpAlloc::new("demo-bump", 4096, 1);
        demo_alloc(&alloc, &alloc, || println!("alloc: {:?}", alloc));
    }) {
        match panicked.downcast_ref::<String>() {
            Some(msg) => {
                println!("DumbBumpAlloc panicked: {}", msg);
            }
            None => {
                println!("DumbBumpAlloc panicked");
            }
        }
    }

    // The below is (rightly) rejected: It is not valid to have the
    // vector outlive the borrowed allocator it is referencing.
    //
    // let v = {
    //     let alloc = DumbBumpAlloc::new("demo2", 4096, 1);
    //     let mut v = Vec::new_in(&alloc);
    //     for i in 1..4 { v.push(i); }
    //     v
    // };

    let alloc = DumbBumpAlloc::new("demo-bump", 4096, 1);
    for i in 0..100 {
        let r = ::std::thread::scoped(|| {
            let v = Vec::new_in(&alloc);
            for j in 0..10 {
                v.push(j);
            }
        });
    }

    println!("got here");
}
