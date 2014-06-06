#![no_std]
#![crate_type="lib"]
#[lang="sized"] pub trait Sized { }

pub fn step() {
    let mut f = ();
    let mut g = ();
    loop
    {
        let _f = &mut f;
        let _g = &mut g;
        break;
    }

    &mut f;
}
