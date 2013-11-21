#[feature(managed_boxes)];

#[allow(unused_imports)];
use std::cast;
use std::libc;
use std::local_data;
use std::ptr;
use std::rt::local_heap;
use std::rt::local_heap::{MemoryRegion, Box};
use std::rt::{DumpedRegs,Registers};

type DumpedRegsArea = [u64, ..80];

struct ctxt {
    verbose: bool,
    id: int,
    info: ()
}

impl Clone for ctxt {
    fn clone(&self) -> ctxt {
        if self.verbose {
            println!("cloning ctxt id: {}", self.id);
        }
        ctxt { id: self.id + 1, ..*self }
    }
}

impl Drop for ctxt {
    fn drop(&mut self) {
        println!("dropping ctxt, id: {}", self.id);
    }
}

fn walk_managed(mut ctxt: ~ctxt) {
    // Dumping xmm state requires 16-byte alignement (at least when
    // using `movapd`; not yet sure about `fxsave`).
    let action = do_walk;

    // let regs = [0u64, ..80];
    // let r : uint = cast::transmute(&regs);
    // let r = (r + 16) & (!15); // round-up to 16-byte alignment.

    // let mut regs : DumpedRegs = cast::transmute(r);
    let mut regs : DumpedRegs = DumpedRegs::new_unfilled();

    let c : int;
    let dr : int;
    let ir : int;
    unsafe { c = cast::transmute(ctxt); ctxt = cast::transmute(c); }
    unsafe {
        dr = cast::transmute(&regs);
        struct FakeDumpedRegs { regs: ~Registers }
        let fdr : FakeDumpedRegs = cast::transmute(regs);
        let pir : *int = cast::transmute(&fdr.regs);
        ir = *pir;
        regs = cast::transmute(fdr);
    }

    let a1 = dr;
    let a2 = action as int;
    let a3 = c;

    if ctxt.verbose {
        println!("about to regs.dump (regs: 0x{:x} \\{ .regs: 0x{:x} \\}, \
                                      action: 0x{:x}, \
                                      ctxt: 0x{:x}), \
                  regs: {:?} ctxt: {:?} at 0x{:x}",
                 a1, ir, a2, a3, regs, ctxt, a3);
    } else {
        println!("about to regs.dump");
    }
    regs.dump(&mut *ctxt, action);
    if ctxt.verbose {
        println!("post the regs.dump (regs: 0x{:x}, \
                                      action: 0x{:x}, \
                                      ctxt: 0x{:x}), \
                  regs: {:?} ctxt: {:?} at 0x{:x}",
                 a1, a2, a3, regs, ctxt, a3);
    } else {
        println!("post the regs.dump");
    }
}

fn subroutine_alloc() {
    // enum Ll { Cons(int, @Ll), Nil }
    // fn alloc_some() -> ~Ll { ~Cons(1, @Cons(2, @Cons(3, @Nil))) }
    // let mut x = alloc_some();
    // println!("allocated x: {:?}", x);
    // *x = Nil;

    let mut x = ~Some(@3);

    println!("allocated x: {:?}", x);

    traverse_live_allocs();

    *x = None;

    println!("overwrote x: {:?}", x);

    traverse_live_allocs();
}

fn traverse_live_allocs() {
    let bp : *mut Box = local_heap::live_allocs();
    println!("bp: {:?}", bp);
    let mut cursor = bp;
    let mut count = 0;
    if cursor != ptr::mut_null() {
        loop {
            unsafe {
                println!("{: >5d}: *cursor: {:?}", count, *cursor);
                cursor = (*cursor).next;
            }
            count += 1;
            if cursor == ptr::mut_null() { break; }
            if cursor == bp { fail!("uh oh"); }
        }
    }
}

extern "C" fn do_walk(mut regs: &mut Registers, mut ctxt: &mut ctxt, _:*()) {
    use std::rt::task::Task;
    use std::rt::local::Local;

    println!("do_walk");
    let a1 : int;
    let ctxt_ptr : int;
    unsafe {
        a1 = cast::transmute(regs);
        ctxt_ptr = cast::transmute(ctxt);

        // Apparently it is super-important that I restore the
        // transmutes before allowing any allocation (incl. ~-), such
        // as that performed by format! within println!.
        //
        // Or maybe error I am seeing is just non-deterministic.  Grr.
        ctxt = cast::transmute(ctxt_ptr);
        regs = cast::transmute(a1);
        println!("do_walk(regs: 0x{:x}, ctxt: 0x{:x})", a1, ctxt_ptr);
    }

    println!("about to enter subroutine");

    subroutine_alloc();

    println!("completed with subroutine");

    traverse_live_allocs();

    let c : int;
    unsafe {
        c = cast::transmute(ctxt);
        ctxt = cast::transmute(c);
    }
    if ctxt.verbose {
        println!("got to do_walk, regs: {:?} ctxt: {:?} at 0x{:x}",
                 regs, ctxt, c as libc::c_int);
    } else {
        println!("got to do_walk");
    }

    fn traverse_local_heap_structure() {
        Local::borrow(|task: &mut Task| {

                struct MyLocalHeap { // XXX keep synced w/ local_heap::LocalHeap
                    memory_region: MemoryRegion,
                    poison_on_free: bool,
                    live_allocs: *mut Box,
                }

                let hp : &MyLocalHeap = unsafe { cast::transmute(&task.heap) };
                println!("hp: {:?}", hp);
            });
    }
}

fn main() {
    println!("Hello world.");
    let ctxt = ~ctxt { verbose: false, id: 100, info: () };
    walk_managed(ctxt);
}
