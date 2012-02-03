type foo = { mutable z : fn@() };

fn nop() { }
fn nop_foo(_x : @foo) { }

fn main() {
    let w = @{ mutable z: fn@() { nop() } };
    let x = fn@() { nop_foo(w); };
    w.z = x;
}