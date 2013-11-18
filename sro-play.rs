#[allow(unused_imports)];
use std::cast;
use std::libc;
use std::local_data;
use std::rt::dump_registers;

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
        let action : *libc::c_void = cast::transmute(do_walk_managed);
        let ctxt_cloned = ctxt.clone();
        let c : *libc::c_void = cast::transmute(ctxt);
        let a1 = cast::transmute(r);
        let a2 = action;
        let a3 = c;
        println!("about to dump_registers(0x{:x}, 0x{:x}, 0x{:x}), ctxt: {:?} at 0x{:x}",
                 a1 as libc::c_int, a2, a3, ctxt_cloned, c as libc::c_int);
        dump_registers(a1, a2, a3);
    }
}

extern "C" fn do_walk_managed(_regs: *libc::c_void, _action: *libc::c_void, ctxt_ptr: *libc::c_void) {
    println!("do_walk_managed(0x{:x}, 0x{:x}, 0x{:x})",
             _regs as libc::c_int,
             _action as libc::c_int,
             ctxt_ptr as libc::c_int);
    let c : *libc::c_void;
    let ctxt_cloned;
    unsafe {
        let ctxt: ~ctxt = cast::transmute(ctxt_ptr);
        ctxt_cloned = ctxt.clone();
        c = cast::transmute(ctxt);
    }
    println!("got to do_walk_managed, ctxt: {:?} at 0x{:x}", ctxt_cloned, c as libc::c_int);
}

fn main() {
    println!("Hello world.");
    let ctxt = ~ctxt { id: 100, info: () };
    walk_managed(ctxt);
}
