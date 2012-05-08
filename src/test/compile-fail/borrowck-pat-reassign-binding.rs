// compile-flags:--borrowck=err
// xfail-pretty -- comments are infaithfully preserved

fn main() {
    let mut x: option<int> = none;
    alt x { //! NOTE Loan of mutable local variable granted here
      none {}
      some(i) {
        // Not ok: i is an outstanding ptr into x.
        x = some(i+1);
        //!^ ERROR Cannot assign to mutable local variable due to outstanding loan
      }
    }
}
