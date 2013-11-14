// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use libc::{c_void, size_t, free, malloc, realloc};
use option::{Option, Some, None};
use ptr::{RawPtr, mut_null};
use unstable::intrinsics::TyDesc;
use unstable::intrinsics::abort;
use unstable::raw;
use mem::size_of;

#[inline]
pub fn get_box_size(body_size: uint, body_align: uint) -> uint {
    let header_size = size_of::<raw::Box<()>>();
    let total_size = align_to(header_size, body_align) + body_size;
    total_size
}

// Rounds |size| to the nearest |alignment|. Invariant: |alignment| is a power
// of two.
#[inline]
fn align_to(size: uint, align: uint) -> uint {
    assert!(align != 0);
    (size + align - 1) & !(align - 1)
}

/// A wrapper around libc::malloc, aborting on out-of-memory
#[inline]
pub unsafe fn malloc_raw(size: uint) -> *mut u8 {
    // `malloc(0)` may allocate, but it may also return a null pointer
    // http://pubs.opengroup.org/onlinepubs/9699919799/functions/malloc.html
    if size == 0 {
        mut_null()
    } else {
        let p = malloc(size as size_t);
        if p.is_null() {
            // we need a non-allocating way to print an error here
            abort();
        }
        p as *mut u8
    }
}

/// Frees a block of memory previously returned from malloc_raw.
pub unsafe fn free_raw(ptr: *u8) {
    free(ptr as *mut c_void);
}

/// A wrapper around libc::realloc, aborting on out-of-memory
#[inline]
pub unsafe fn realloc_raw(ptr: *mut u8, size: uint) -> *mut u8 {
    // `realloc(ptr, 0)` may allocate, but it may also return a null pointer
    // http://pubs.opengroup.org/onlinepubs/9699919799/functions/realloc.html
    if size == 0 {
        free(ptr as *mut c_void);
        mut_null()
    } else {
        let p = realloc(ptr as *mut c_void, size as size_t);
        if p.is_null() {
            // we need a non-allocating way to print an error here
            abort();
        }
        p as *mut u8
    }
}

pub struct ExchangeCallbacks {
    malloc_no_ty:   fn(ptr: *u8, size: uint),
    malloc_precise: fn(ptr: *u8, size: uint, td: *TyDesc),
    free:           fn(ptr: *u8),
}
static mut current_exchange_callbacks: Option<ExchangeCallbacks> = None;

/// The allocator for unique pointers without contained managed pointers.
#[cfg(not(test))]
#[lang="exchange_malloc"]
#[inline]
pub unsafe fn exchange_malloc(size: uint) -> *u8 {
    exchange_malloc_no_ty(size) as *u8
}

#[cfg(not(test),not(stage0))]
#[lang="exchange_malloc_precise"]
#[inline]
pub unsafe fn exchange_malloc_precise(td: *u8, size: uint) -> *u8 {
    exchange_malloc_precise1(td, size)
}

#[cfg(not(test),not(stage0))]
unsafe fn exchange_malloc_precise1(td: *u8, size: uint) -> *u8 {
    let td = td as *TyDesc;
    let ret = malloc_raw(size) as *u8;
    match current_exchange_callbacks {
        None => {}, Some(cb) => (cb.malloc_precise)(ret, size, td)
    }
    ret
}

#[cfg(not(test))]
unsafe fn exchange_malloc_no_ty(size: uint) -> *u8 {
    let ret = malloc_raw(size) as *u8;
    match current_exchange_callbacks {
        None => {}, Some(cb) => (cb.malloc_no_ty)(ret, size)
    }
    ret
}


// FIXME: #7496
#[cfg(not(test), stage0)]
#[lang="closure_exchange_malloc"]
#[inline]
pub unsafe fn closure_exchange_malloc_(td: *u8, size: uint) -> *u8 {
    closure_exchange_malloc0(td, size)
}

#[cfg(not(stage0))]
#[lang="proc_malloc_precise"]
#[inline]
pub unsafe fn proc_malloc_precise(td: *u8, size: uint) -> *u8 {
    let td = td as *TyDesc;
    closure_exchange_malloc_precise1(td, size)
}

// FIXME: #7496
#[cfg(not(test), not(stage0))]
#[lang="closure_exchange_malloc"]
#[inline]
pub unsafe fn closure_exchange_malloc_(drop_glue: fn(*mut u8), size: uint, align: uint) -> *u8 {
    closure_exchange_malloc_no_ty(drop_glue, size, align)
}

#[inline]
#[cfg(stage0)]
unsafe fn closure_exchange_malloc0(td: *u8, size: uint) -> *u8 {
    let td = td as *TyDesc;
    let size = size;

    assert!(td.is_not_null());

    let total_size = get_box_size(size, (*td).align);
    let p = malloc_raw(total_size);

    let alloc = p as *mut raw::Box<()>;
    (*alloc).type_desc = td;

    alloc as *u8
}


#[inline]
#[cfg(not(stage0))]
unsafe fn closure_exchange_malloc_no_ty(drop_glue: fn(*mut u8), size: uint, align: uint) -> *u8 {
    let total_size = get_box_size(size, align);
    let p = malloc_raw(total_size);

    let alloc = p as *mut raw::Box<()>;
    (*alloc).drop_glue = drop_glue;

    let ret = alloc as *u8;
    match current_exchange_callbacks {
        None => {}, Some(cb) => (cb.malloc_no_ty)(ret, size)
    }
    ret
}

#[inline]
#[cfg(not(stage0))]
unsafe fn closure_exchange_malloc_precise1(td: *TyDesc, size: uint) -> *u8 {
    let total_size = get_box_size(size, (*td).align);
    let p = malloc_raw(total_size);

    let alloc = p as *mut raw::Box<()>;
    (*alloc).drop_glue = (*td).drop_glue;

    let ret = alloc as *u8;
    match current_exchange_callbacks {
        None => {}, Some(cb) => (cb.malloc_no_ty)(ret, size)
    }
    ret
}

// NB: Calls to free CANNOT be allowed to fail, as throwing an exception from
// inside a landing pad may corrupt the state of the exception handler.
#[cfg(not(test))]
#[lang="exchange_free"]
#[inline]
pub unsafe fn exchange_free_(ptr: *u8) {
    match current_exchange_callbacks { None => {}, Some(cb) => (cb.free)(ptr) }
    exchange_free(ptr)
}

#[inline]
pub unsafe fn exchange_free(ptr: *u8) {
    match current_exchange_callbacks { None => {}, Some(cb) => (cb.free)(ptr) }
    free(ptr as *mut c_void);
}

#[cfg(test)]
mod bench {
    use extra::test::BenchHarness;

    #[bench]
    fn alloc_owned_small(bh: &mut BenchHarness) {
        bh.iter(|| {
            ~10;
        })
    }

    #[bench]
    fn alloc_owned_big(bh: &mut BenchHarness) {
        bh.iter(|| {
            ~[10, ..1000];
        })
    }
}
