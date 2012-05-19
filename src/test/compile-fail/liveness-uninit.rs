fn foo(x: int) { log(debug, x); }

fn main() {
	let x: int;
	foo(x); //! ERROR use of variable that may not have been initialized
}
