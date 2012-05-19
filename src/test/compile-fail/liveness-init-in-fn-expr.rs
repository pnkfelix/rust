fn main() {
    let f = fn@() -> int {
        let i: int;
        ret i; //! ERROR use of variable that may not have been initialized
    };
    log(error, f());
}
