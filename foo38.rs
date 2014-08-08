#![feature(intrinsics)]
#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="sized"] pub trait Sized { }

#[lang = "owned_box"]
pub struct Box<T>(*mut T);
pub enum Option<T> { None, Some(T), }

// Attempting to recreate warning for 
//   src/libcollections/trie.rs:344:48: 350:26
//     error: Storage at `(children[..]->trie::External)` is left ...
// which seems to be falsely arising, since there should not be a
// move occurring in this case, since the pattern is of the form
// `External(stored, _)`, and stored is an int (i.e. :Copy), so the
// whole thing should be pass by copy, with no drop obligation.

pub struct TrieNode<'a,T> {
    children: &'a [Child<'a,T>],
}

pub enum Child<'a,T> {
    Internal(Box<TrieNode<'a,T>>),
    External(uint, T),
}

pub fn foo<'a, T>(node_orig: *mut TrieNode<T>, idx: uint) {
    let mut _node = node_orig;
    let children = unsafe { &mut (*_node).children };
    match children[idx] {
        Internal(ref _x) => {}
        External(_stored, _) => {}
    }
    no_op();
}

fn no_op() { }
