#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="sized"] pub trait Sized { }

#[lang = "owned_box"]
pub struct Box<T>(*mut T);
pub enum Option<T> { None, Some(T), }

pub static SIZE: uint = 2;


pub struct TrieNode<T> {
    _count: uint,
    children: [Child<T>, ..SIZE],
}

pub enum Child<T> {
    Internal(Box<TrieNode<T>>),
    External(uint, T),
    Nothing
}

pub fn foo<'a, T>(node_orig: &'a TrieNode<T>, idx: uint) -> Option<&'a T> {
    let mut idx = idx;
    let mut node = node_orig;
    loop {
        match node.children[idx] {
            Internal(ref x) => node = &**x,
            External(stored, ref value) =>
                if stored == idx {
                    return Some(value)
                } else {
                    return None
                },
            Nothing => return None,
        }
        idx += 1;
    }
}
