fn test(cond: bool) {
    let mut v: int;
    v = v + 1; //! ERROR use of variable that may not have been initialized
}

fn main() {
    test(true);
}
