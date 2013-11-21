#[feature(managed_boxes)];
#[allow(unused_imports)];
use std::ptr;
use std::rt::local_heap;
use std::rt::local_heap::{MemoryRegion, Box};

fn sub(_prefix: &'static str, _x: ~Option<@int>) -> ~Option<@int> {
    println!("{} x: {:?}", _prefix, _x);
    traverse_live_allocs();
    _x
}

fn subroutine_alloc() {
    #[allow(dead_assignment)];
    let mut x = ~None;
    x = sub("naughtyet", x);

    x = ~Some(@3);
    x = sub("allocated", x);

    *x = None;
    x = sub("overwrote", x);
}

fn main() { subroutine_alloc() }

fn traverse_live_allocs() {
    let bp : *mut Box = local_heap::live_allocs();
    println!("bp: {:?}", bp);
    let mut cursor = bp;
    let mut count = 0;
    if cursor != ptr::mut_null() {
        loop {
            unsafe {
                println!("{: >5d}: *cursor: \\{ ref_count: \
                         {}\n                  type_desc: \
                         {}\n                  prev: \
                         {}\n                  next: \
                         {}\n                  data: \
                         {:?}               \\}",
                         count,
                         (*cursor).ref_count,
                         (*cursor).type_desc,
                         (*cursor).prev,
                         (*cursor).next,
                         (*cursor).data );
                cursor = (*cursor).next;
            }
            count += 1;
            if cursor == ptr::mut_null() { break; }
            if cursor == bp { fail!("uh oh"); }
        }
    }
}
