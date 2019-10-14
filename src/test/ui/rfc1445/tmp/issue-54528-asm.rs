#![feature(asm)]

fn main() {
    let mut a = &mut 3;
    let b = &*a;
    unsafe {
        asm!("nop" : "=r"(a));  //[ast]~ ERROR cannot assign to `a` because it is borrowed
                                // No MIR error, this is a shallow write.
    }
    let _c = b;
    let _d = *a;
}
