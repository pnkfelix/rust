fn f() -> int {
    let mut x: int;
    while 1 == 1 { x = 10; }
    ret x; //! ERROR use of variable that may not have been initialized
}

fn main() { f(); }
