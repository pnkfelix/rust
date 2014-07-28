#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }
#[lang="send"]  pub trait Send { }


/// A type that represents a uniquely-owned value.
#[lang = "owned_box"]
#[unstable = "custom allocators will add an additional type parameter (with default)"]
pub struct Box<T>(*mut T);

pub trait Writer { }

pub fn drop<T>(_x: T) { }

pub enum Option<T> { None, Some(T), }

pub fn set_stderr(_stderr: Box<Writer + Send>) -> Option<Box<Writer + Send>> {
    loop { }
}

/// Remove the first Node and return it, or None if the list is empty
pub fn foo<T>() {
    // a snippet taken from rustdoc::test::runtest

    struct ChanWriter;
    impl Writer for ChanWriter {}
    let w1 = ChanWriter;
    let old = set_stderr(box w1);

    let my_proc = proc() {
        match old {
            Some(old) => {
                // Chop off the `Send` bound.
                let old : Box<Writer> = old;
                old
            }
            None => loop { }
        };
        loop { }
    };
    my_proc()
}
