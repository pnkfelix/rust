#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

extern crate url;
use url; //~ ERROR unresolved import (maybe you meant `url::*`?)

mod a {
    pub static x : int = 3;
    pub static y : int = 4;
    pub static z : int = 5;
}

mod b {
    use a::x;
    use m = a::y;
    use a::z as n;

    pub fn foo() -> int { x + m + n }
}

pub fn foo() -> int {
    b::foo()
}
