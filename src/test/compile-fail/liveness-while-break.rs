fn test(cond: bool) {
    let v;
    while cond {
        v = 3;
        break;
    }
    #debug["%d", v]; //! ERROR use of variable that may not have been initialized
}

fn main() {
    test(true);
}
