#[derive(PartialEq, Eq)]
struct S;

fn main() {
    const C: &S = &S;
    match C {
        C => {}
    }
}
