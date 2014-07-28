#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub enum Result<T,E> { Ok(T), Err(E) }

pub fn foo<X,Y>(c: || -> Result<X,Y>,
                x: |X| -> Result<X,Y>) -> Result<X,Y> {
    let s = c();
    let ret = match s {
        Err(_) => s,
        Ok(content) => x(content),
    };
    c();
    ret
}
