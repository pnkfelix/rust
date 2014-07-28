#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub fn drop<T>(_x: T) { }

pub enum Result<T, E> { Ok(T), Err(E), }

// originally `Result::or`
pub fn foo<T,E>(s: Result<T, E>, res: Result<T,E>) -> Result<T,E> {
    match s {
        Err(_) => {
            drop(s);
            res
        }
        Ok(_) => {
            drop(res);
            s
        }
    }
}
