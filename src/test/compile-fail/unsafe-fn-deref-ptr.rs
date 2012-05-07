// -*- rust -*-

fn f(p: *u8) -> u8 {
    ret *p; //! ERROR unsafe operation requires unsafe function or block
}

fn main() {
}
