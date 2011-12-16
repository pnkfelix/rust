// error-pattern: expecting ;, found {

use std;
import std::math;

fn main() {
    fn f(_i: block() -> uint) {}
    let v = [-1f, 0f, 1f, 2f, 3f];
    let _z = vec::foldl(f, v) { |x, _y| x } { || 22u };
}
