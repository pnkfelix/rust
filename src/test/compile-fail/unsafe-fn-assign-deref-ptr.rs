// -*- rust -*-

fn f(p: *u8) {
    *p = 0u8; //! ERROR unsafe operation requires unsafe function or block
    ret;
}

fn main() {
}
