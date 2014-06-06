#![no_std]
#![crate_type="lib"]
#[lang="sized"] pub trait Sized { }

struct S;
#[lang="drop"]
pub trait Drop {
    /// The `drop` method, called when the value goes out of scope.
    fn drop(&mut self);
}
impl Drop for S {
    fn drop(&mut self) { }
}

#[cold] #[inline(never)] // this is the slow path, always
#[lang="fail_"]
#[cfg(not(test))]
fn fail_(expr: *u8, file: *u8, line: uint) -> ! {
    loop {}
}

pub fn step(f: bool) {
    let mut g = S;
    loop
    {
        let _g = g;

        if f {
            g = S;
            continue;
        }

        // break;
        fail_(0 as *u8, 0 as *u8, 0);
    }
}
