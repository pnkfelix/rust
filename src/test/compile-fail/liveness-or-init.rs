fn main() {
    let i: int;

    log(debug, false || { i = 5; true });
    log(debug, i); //! ERROR use of variable that may not have been initialized
}
