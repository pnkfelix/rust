/*
Can we bind native things?
*/

#[abi = "cdecl"]
native mod rustrt {
    fn strlen(c: *u8) -> ctypes::c_int;
}

fn main() {
    let strlen = rustrt::strlen(_);
    str::as_buf("foo") {|b|
        assert strlen(b) == 3i32;
    }
}

