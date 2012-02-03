// -*- rust -*-

unsafe fn f(x: int, y: int) -> int { ret x + y; }

fn main() {
    let x = f(3, _);
    //!^ ERROR safe function calls function marked unsafe
    let y = x(4);
}
