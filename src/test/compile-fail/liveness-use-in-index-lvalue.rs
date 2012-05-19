fn test() {
    let w: [int];
    w[5] = 0; //! ERROR use of variable that may not have been initialized
}

fn main() { test(); }
