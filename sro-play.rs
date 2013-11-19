#[allow(unused_imports)];
use std::cast;
use std::libc;
use std::local_data;
use std::rt::DumpedRegs;

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

fn walk_managed(ctxt: ~ctxt) {
    // Dumping xmm state requires 16-byte alignement (at least when
    // using `movapd`; not yet sure about `fxsave`).
    unsafe {
        let regs = [0u64, ..80];
        let r : uint = cast::transmute(&regs);
        let r = (r + 16) & (!15); // round-up to 16-byte alignment.
        let action = do_walk_managed;
        let ctxt_cloned = ctxt.clone();
        let c : *libc::c_void = cast::transmute(ctxt);
        let mut regs : DumpedRegs = cast::transmute(r);
        let a1 : int = cast::transmute(regs);
        let a2 = action as libc::c_int;
        let a3 = c as libc::c_int;
        println!("about to dump_registers(regs: 0x{:x}, \
                                          action: 0x{:x}, \
                                          ctxt: 0x{:x}), \
                  ctxt: {:?} at 0x{:x}",
                 a1, a2, a3, ctxt_cloned, a3);
        let mut ctxt : ~ctxt = cast::transmute(c);
        regs = cast::transmute(a1);
        regs.dump(ctxt, action);
    }
}

extern "C" fn do_walk_managed(regs: &mut DumpedRegs, mut ctxt: &mut ctxt) {
    unsafe {
        println!("do_walk_managed");
        let a1 : int = cast::transmute(regs);
        let ctxt_ptr : *() = cast::transmute(ctxt);
        println!("do_walk_managed(regs: 0x{:x}, ctxt: 0x{:x})",
                 a1.clone() as libc::c_int,
                 ctxt_ptr as libc::c_int);
        regs = cast::transmute(a1);
        ctxt = cast::transmute(ctxt_ptr);
    }
    let c : *libc::c_void;
    let ctxt_cloned;
    unsafe {
        ctxt_cloned = ctxt.clone();
        c = cast::transmute(ctxt);
    }
    println!("got to do_walk_managed, regs: {:?} ctxt: {:?} at 0x{:x}",
             regs, ctxt_cloned, c as libc::c_int);
}

fn main() {
    println!("Hello world.");
    let ctxt = ~ctxt { id: 100, info: () };
    walk_managed(ctxt);
}
