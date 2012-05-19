fn test(cond: bool) {
    let v: int;
    v += 1; //! ERROR use of variable that may not have been initialized
}

fn main() {
    test(true);
}
