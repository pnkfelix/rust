#[allow(unused_imports)];
use std::cast;
use std::libc;
use std::local_data;
use std::rt::{DumpedRegs,Registers};

type DumpedRegsArea = [u64, ..80];

struct ctxt {
    id: int,
    info: ()
}

impl Clone for ctxt {
    fn clone(&self) -> ctxt { ctxt { id: self.id + 1, info: () } }
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

    println!("about to regs.dump (regs: 0x{:x} \\{ .regs: 0x{:x} \\}, \
                                  action: 0x{:x}, \
                                  ctxt: 0x{:x}), \
              regs: {:?} ctxt: {:?} at 0x{:x}",
             a1, ir, a2, a3, regs, ctxt, a3);
    regs.dump(&mut *ctxt, action);
    println!("post the regs.dump (regs: 0x{:x}, \
                                  action: 0x{:x}, \
                                  ctxt: 0x{:x}), \
              regs: {:?} ctxt: {:?} at 0x{:x}",
             a1, a2, a3, regs, ctxt, a3);
}

extern "C" fn do_walk(mut regs: &mut Registers, mut ctxt: &mut ctxt, _:*()) {
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
    let c : int;
    unsafe {
        c = cast::transmute(ctxt);
        ctxt = cast::transmute(c);
    }
    println!("got to do_walk, regs: {:?} ctxt: {:?} at 0x{:x}",
             regs, ctxt, c as libc::c_int);
}

fn main() {
    println!("Hello world.");
    let ctxt = ~ctxt { id: 100, info: () };
    walk_managed(ctxt);
}
