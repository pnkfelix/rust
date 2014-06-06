#![no_std]
#![crate_type="lib"]

/// Types with a constant size known at compile-time.
#[lang="sized"]
pub trait Sized {
    // Empty.
}

#[lang="drop"]
pub trait Drop {
    /// The `drop` method, called when the value goes out of scope.
    fn drop(&mut self);
}

pub struct S;
impl Drop for S { fn drop(&mut self) { } }
impl S {
    fn foo(&self) -> int { 3 }
}

pub extern fn do_call(f: & &S) {
    (**f).foo();
    0;
}
