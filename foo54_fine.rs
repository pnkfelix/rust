#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub trait Float {
    fn infinity() -> Self;
    fn neg_infinity() -> Self;
}

pub static INFINITY: f32 = 1.0_f32/0.0_f32;
pub static NEG_INFINITY: f32 = -1.0_f32/0.0_f32;

impl Float for f32 {
    fn infinity() -> f32 { INFINITY }
    fn neg_infinity() -> f32 { NEG_INFINITY }
}

fn foo(s: f32) -> bool {
    s == Float::infinity() || s == Float::neg_infinity()
}
