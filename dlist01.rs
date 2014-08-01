#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

#[lang = "owned_box"]
#[unstable = "custom allocators will add an additional type parameter (with default)"]
pub struct Box<T>(*mut T);

mod mem {
    pub fn replace<T>(_dest: &mut T, mut _src: T) -> T { loop { } }
}

pub fn drop<T>(_x: T) { }

pub enum Option<T> { None, Some(T), }

impl<T> Option<T> {
    pub fn take(&mut self) -> Option<T> {
        mem::replace(self, None)
    }
    pub fn map<U>(self, f: |T| -> U) -> Option<U> {
        match self { Some(x) => Some(f(x)), None => None }
    }
}

/// Set the .prev field on `next`, then return `Some(next)`
fn link_with_prev<T>(mut next: Box<Node<T>>, prev: Rawlink<Node<T>>)
                  -> Link<T> {
    next.prev = prev;
    Some(next)
}

/// A doubly-linked list.
pub struct DList<T> {
    length: uint,
    list_head: Link<T>,
    list_tail: Rawlink<Node<T>>,
}

type Link<T> = Option<Box<Node<T>>>;
pub struct Rawlink<T>;

pub struct Node<T> {
    next: Link<T>,
    prev: Rawlink<Node<T>>,
}

impl<T> Rawlink<T> {
    fn none() -> Rawlink<T> {
        Rawlink
    }
}

impl<T> DList<T> {
    /// Remove the first Node and return it, or None if the list is empty
    pub fn foo(&mut self) -> Option<Box<Node<T>>> {
        self.list_head.take().map(|mut front_node| {
            self.length -= 1;
            match front_node.next.take() {
                Some(node) => self.list_head = link_with_prev(node, Rawlink::none()),
                None => self.list_tail = Rawlink::none()
            }
            front_node
        })
    }
}
