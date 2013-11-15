use std::cast;
use std::libc;
use std::local_data;

type DumpedRegsArea = [u64, ..80];

struct ctxt {
    id: int,
    info: ()
}

impl Drop for ctxt {
    fn drop(&mut self) {
        println!("dropping ctxt, id: {}", self.id);
    }
}

fn walk_managed(c: ~ctxt) {
    // Dumping xmm state requires 16-byte alignement (at least when
    // using `movapd`; not yet sure about `fxsave`).
    let regs = [0u64, ..80];
    let r : uint = cast::transmute(&regs);
    let r = (r + 16) & (!15); // round-up to 16-byte alignment.
    let action : *libc::c_void = cast::transmute(do_walk_managed);
    let c : *libc::c_void = cast::transmute(c);
    dump_registers(cast::transmute(r), action, c);
}

fn do_walk_managed(c: ~ctxt) {
    println!("got to do_walk_managed, ctxt: {:?}", c);
}

fn main() {
    println!("Hello world.");
    unsafe {
        do local_data::each_retained_ptr |cv| {
            println!("{:?}", cv);
        }
    }
}
