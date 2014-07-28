#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub fn drop<T>(_x: T) { }

pub enum Option<T> { None, Some(T), }

pub struct Cell<T> {
    value: T,
}

/// Remove the first Node and return it, or None if the list is empty
pub fn foo<T>(self_: &mut Cell<T>,
              taken: Option<T>) {
    let f = |front_node: Option<T>| {
    //                                                          // NEEDS_DROP={front_node}
        match front_node { // by-move match consumes front_node ...
            Some(node) => {
    //                                                          // NEEDS_DROP={node}
                self_.value = node
    //                                                          // NEEDS_DROP={}
            }
            None => {
    //                                                          // NEEDS_DROP={}
            }
        } // ... this should be fine
    };

    f(taken)
}
