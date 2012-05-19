fn f() -> int {
	let x: int;
	ret x; //! ERROR use of variable that may not have been initialized
}

fn main() { f(); }
