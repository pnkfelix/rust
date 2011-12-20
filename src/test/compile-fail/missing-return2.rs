// error-pattern: expected int but found ()

fn f() -> int {
    alt true { true { } }
}

fn main() { }
