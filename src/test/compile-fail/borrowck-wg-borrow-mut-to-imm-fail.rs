fn main() {
    let mut b = ~3;
    let _x = &mut *b;
    let mut y = /*move*/ b; //~ ERROR moving out of mutable local variable prohibited
    *y += 1;
}

