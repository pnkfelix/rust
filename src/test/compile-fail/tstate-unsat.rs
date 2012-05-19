pure fn is_even(i: int) -> bool { (i%2) == 0 }
fn even(i: int) : is_even(i) -> int { i }

fn main() {
	let x: int;
        even(x); //! ERROR unsatisfied precondition
}
