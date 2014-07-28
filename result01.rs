#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub fn drop<T>(_x: T) { }

pub enum Option<T> { None, Some(T), }
pub enum Result<T, E> { Ok(T), Err(E), }

pub fn foo<T,E>(s: Result<T, E>) -> Option<T> {
    match s {
        Ok(x)  => { Some(x) },
        Err(_s) => { None },
    }
}
