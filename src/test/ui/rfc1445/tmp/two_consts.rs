#![crate_type="lib"]

#[derive(PartialEq, Eq)]
pub struct S(u32);

pub struct N(u32);

#[derive(PartialEq, Eq)]
pub struct W<X>(X);

impl PartialEq for N {
    fn eq(&self, rhs: &Self) -> bool {
        self.0.eq(&rhs.0)
    }
}

impl Eq for N { }

pub const S1: S = S(1);
pub const S2: S = S(2);
pub const N3: N = N(3);
pub const N4: N = N(4);
pub const WSS56: W<(S,S)> = W((S(5),S(6)));
pub const WSN78: W<(S,N)> = W((S(7),N(8)));

fn main() {
    match S(1) {
        S1 => println!("S1"),
        _ => println!("other"),
    }
}
