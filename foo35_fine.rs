#![feature(intrinsics)]
#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="sized"] pub trait Sized { }

#[lang = "owned_box"]
pub struct Box<T>(*mut T);
pub enum Option<T> { None, Some(T), }

pub static SIZE: uint = 2;


pub struct TrieNode<'a,T> {
    _count: uint,
    children: &'a [Child<'a,T>],
}

pub enum Child<'a,T> {
    Internal(Box<TrieNode<'a,T>>),
    External(uint, T),
    Nothing
}

extern "rust-intrinsic" {
    pub fn transmute<T,U>(e: T) -> U;
}

// This was an attempt to capture another ICE from trie.rs back when
// the LpInterior(Element(_)) cases in `LoanPath::to_type` did not
// fall through to the second case properly. But I am not sure I ever
// actually saw the problem manifest itself on this narrowed test case
// (As in, do not stress about trying to incorporate this test as is.)
pub fn foo<'a, T>(node_orig: *mut TrieNode<T>, idx: uint) -> Option<&'a T> {
    let mut idx = idx;
    let mut node = node_orig;
    loop {
        let children = unsafe { &mut (*node).children };
        match children[idx] {
            Internal(ref x) => node = unsafe { transmute(&**x) },
            External(_stored, _) => return None,
            Nothing => return None,
        }
        idx += 1;
    }
}
