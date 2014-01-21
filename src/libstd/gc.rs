// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Task-local garbage-collected boxes

The `Gc` type provides shared ownership of an immutable value. Destruction is not deterministic, and
will occur some time between every `Gc` handle being gone and the end of the task. The garbage
collector is task-local so `Gc<T>` is not sendable.

*/

#[allow(experimental)];

use kinds::{Send,Testate};
use cell::{RefCell,RefMut};
use clone::{Clone, DeepClone};
use container::Container;
use managed;
use ops::Drop;
use option::{Option, None, Some};
use ptr;
use vec::OwnedVector;

/// A Guardian mediates the transfer of assets from dead managed
/// data back to the program for disposal.
///
/// An "asset" here means "a struct implementing the Drop trait";
/// usually this means the struct holds some resource that the GC is
/// not itself responsible for disposing of.
///
/// Further explanation:
///
/// The Garbage Collector (GC) is responsible for identifying dead
/// managed data; it does so at arbitrary points in the program's
/// execution.  Much managed data will be plain old bytes that the GC
/// deallocates directly; but some of the dead managed data may have
/// owned resources that need special handling.
///
/// Examples of resources that the GC could encounter include:
///
///   * a block of memory (*T) shared across multiple tasks, or
///
///   * a pointer to a black box owned by a native library (such as a
///     file handle).
///
/// Generally disposing of such resources will require running
/// arbitrary user code; thus the above definition of "asset."
///
/// Since the GC runs at unpredictable times, it is not sound for the
/// GC to invoke the arbitrary user code associated with assets
///
/// Instead, in a Guardian-based finalization the program is
/// responsible for:
///
///   1. associating each asset with some guardian, and
///
///   2. disposing of the assets that accumulated in the guardian(s).
///
/// Note that the promptness of disposal (or lack thereof) is entirely
/// up to the mutator.  If different assets have different disposal
/// priorities, then associate them with distinct guardians, and poll
/// them at different rates.
///
/// See also Testate
trait Guardian<A> {
    // Some easy methods: these are called from the mutator.

    /// How many assets are currently awaiting post-processing by the mutator?
    fn num_assets(&self) -> uint;

    /// Extract an asset for custom post-processing.
    fn pull_asset(&mut self) -> Option<A>; // ("pull" b/c pop implies order)

    /// Calls the destructors of at most `n` enqueued assets.
    fn drop_some_assets(&mut self, n: uint);

    /// Calls the destructors for all enqueued assets.
    fn drop_all_assets(&mut self) {
        let n = self.num_assets();
        self.drop_some_assets(n);
    }

    /// Enqueues `asset` for later post-processing.  Called by the GC
    /// at arbitrary points in time; any asynchronous behavior
    /// (e.g. acquiring a lock) should not be done here, but instead
    /// left for the asset post-processing.
    fn receive(&mut self, asset:A);
}

/// A SimpleGuardian is just a queue of gathered assets.
pub struct SimpleGuardian<A> {
    priv assets: ~[A]
}

impl<A> SimpleGuardian<A> {
    fn new() -> SimpleGuardian<A> { SimpleGuardian { assets: ~[] } }
}

// a variation worth considering: a guardian whose receive method also
// enqueues the guardian itself onto a collection of non-empty
// guardians, thus side-stepping the issue of potentially wasting time
// polling a large set of empty guardians.

impl<E> Guardian<E> for SimpleGuardian<E> {
    fn num_assets(&self) -> uint { self.assets.len() }
    fn pull_asset(&mut self) -> Option<E> { self.assets.pop_opt() }
    fn drop_some_assets(&mut self, n: uint) {
        let l = self.assets.len();
        self.assets.truncate(if n < l { l - n } else { 0 });
    }
    fn receive(&mut self, asset:E) { self.assets.push(asset); }
}

/// A Guard is specialized for handling assets of a particular type.
#[unsafe_can_drop_during_gc]
pub struct Guard<E, G> { // G:Guardian<E>
    /// The asset to be handed off by this guard upon its death.
    asset: E,
    priv guardian: G
}

/// Use Discard with simple-minded guardians that only know how to do
/// one thing with assets: destroy them.
#[unsafe_can_drop_during_gc]
pub struct Discard<E, G> { // G:Guardian<~Drop>
    /// The asset to be handed off by this guard upon its death.
    asset: ~E,
    priv guardian: G
}

/// Can is a generic guard that is hard-wired to throw assets into the
/// (per-task) TrashCan.  Note that if a program uses Can, the program
/// is itself responsible for periodically empyting the trash.
///
/// See TrashCan::empty_all.
#[unsafe_can_drop_during_gc]
pub struct Can<E>(~E);

/// The TrashCan is a task-local simple minded guardian.  You can hook
/// up to it via Discard (or Guard, if your type is compatible), or
/// you can just use Can.
pub struct TrashCan {
    priv bucket_list: RefCell<SimpleGuardian<~Drop>>
}

impl TrashCan {
    /// Puts the debris into this trash can for eventual dropping later.
    pub fn discard(&mut self, debris: ~Drop) {
        let mut g = self.bucket_list.borrow_mut();
        g.get().receive(debris);
    }

    /// Drop up to `n` of the enqueued assets in this trash can.
    pub fn empty_some(&mut self, n: uint) {
        let mut bl = self.bucket_list.borrow_mut();
        bl.get().drop_some_assets(n);
    }

    /// Drop all of the enqueued assets in this trash can.
    pub fn empty_all(&mut self) {
        let mut bl = self.bucket_list.borrow_mut();
        bl.get().drop_all_assets();
    }

    /// Create a new trash can.
    pub fn new() -> TrashCan {
        TrashCan {
            bucket_list: RefCell::new(SimpleGuardian::new())
        }
    }
}

// Note to self (can delete before posting for PR): I (Felix) started
// off using Clone here and below to workaround fact that drop takes
// &mut self rather than self-by-value.  But really, assets won't be
// cloneable (and shouldn't be), e.g. a uniquely held file-handle.
// From reading the vec.rs code, it seems like ptr::read_and_zero_ptr
// may have been made exactly for cases like this.

/// Hands 'asset` off to (specialized) `guard` when this dies.
pub fn Guard<A, G:Guardian<A>>(asset: A, guard: G) -> Guard<A,G> {
    Guard{ asset: asset, guardian: guard }
}

#[unsafe_destructor]
impl<E, G:Guardian<E>> Drop for Guard<E,G> {
    fn drop(&mut self) {
        let asset = unsafe {
            let p = &mut self.asset as *mut E;
            ptr::read_and_zero_ptr(p)
        };
        self.guardian.receive(asset);
    }
}

/// Hands `asset` off to (generic) `guard` when this dies.
pub fn Discard<A, G:Guardian<~Drop>>(asset: ~A, guard: G) -> Discard<A, G> {
    Discard{ asset: asset, guardian: guard }
}

#[unsafe_destructor]
impl<E:Drop + Send, G:Guardian<~Drop>> Drop for Discard<E,G> {
    fn drop(&mut self) {
        let asset = unsafe {
            let p = &mut self.asset as *mut ~E;
            ptr::read_and_zero_ptr(p)
        };
        self.guardian.receive(asset as ~Drop);
    }
}

// XXX wait, is this madness?  I probably cannot rely on the
// direct implementation, because we monomorpize Drop impls
// and I doubt that the packagine code for `~E as ~Drop` is
// invariant for all E:Drop.  (It *could* be, but I have no
// reason to beliee that it is at the moment.)
//
// And for all I currently know, that inability to compile generic
// destructors could explain the error messsage I am getting from
// rustc.  Look more tomorrow.

#[unsafe_destructor]
impl<E:Drop + Send> Drop for Can<E> {
    fn drop(&mut self) {
        use rt::task::Task;
        use rt::local::Local;
        let &Can(ref mut ptr_e) = self;
        let (asset, trash_can) = unsafe {
            let p = ptr_e as *mut ~E;
            let asset : ~E = ptr::read_and_zero_ptr(p);
            let task_ptr : Option<*mut Task> = Local::try_unsafe_borrow();
            match task_ptr {
                Some(task) => (asset, &mut (*task).trash),
                None => fail!("Trash Can disposal outside of task")
            }
        };
        let debris : ~Drop = asset as ~Drop;
        trash_can.discard(debris);
    }
}

/// Immutable garbage-collected pointer type
#[lang="gc"]
#[cfg(not(test))]
#[no_send]
#[experimental = "Gc is currently based on reference-counting and will not collect cycles until \
                  task annihilation. For now, cycles need to be broken manually by using `Rc<T>` \
                  with a non-owning `Weak<T>` pointer. A tracing garbage collector is planned."]
pub struct Gc<T> {
    priv ptr: @T
}

#[cfg(test)]
#[no_send]
pub struct Gc<T> {
    priv ptr: @T
}

impl<T: Testate + 'static> Gc<T> {
    /// Construct a new garbage-collected box
    #[inline]
    pub fn new(value: T) -> Gc<T> {
        Gc { ptr: @value }
    }

    /// Borrow the value contained in the garbage-collected box
    #[inline]
    pub fn borrow<'r>(&'r self) -> &'r T {
        &*self.ptr
    }

    /// Determine if two garbage-collected boxes point to the same object
    #[inline]
    pub fn ptr_eq(&self, other: &Gc<T>) -> bool {
        managed::ptr_eq(self.ptr, other.ptr)
    }
}

impl<T:Testate> Clone for Gc<T> {
    /// Clone the pointer only
    #[inline]
    fn clone(&self) -> Gc<T> {
        Gc{ ptr: self.ptr }
    }
}

/// An value that represents the task-local managed heap.
///
/// Use this like `let foo = box(GC) Bar::new(...);`
#[lang="managed_heap"]
#[cfg(not(test))]
pub static GC: () = ();

#[cfg(test)]
pub static GC: () = ();

/// The `Send` bound restricts this to acyclic graphs where it is well-defined.
///
/// A `Freeze` bound would also work, but `Send` *or* `Freeze` cannot be expressed.
impl<T: DeepClone + Send + Testate + 'static> DeepClone for Gc<T> {
    #[inline]
    fn deep_clone(&self) -> Gc<T> {
        Gc::new(self.borrow().deep_clone())
    }
}

#[cfg(test)]
mod tests {
    use prelude::*;
    use super::*;
    use cell::RefCell;

    #[test]
    fn test_clone() {
        let x = Gc::new(RefCell::new(5));
        let y = x.clone();
        x.borrow().with_mut(|inner| {
            *inner = 20;
        });
        assert_eq!(y.borrow().with(|x| *x), 20);
    }

    #[test]
    fn test_deep_clone() {
        let x = Gc::new(RefCell::new(5));
        let y = x.deep_clone();
        x.borrow().with_mut(|inner| {
            *inner = 20;
        });
        assert_eq!(y.borrow().with(|x| *x), 5);
    }

    #[test]
    fn test_simple() {
        let x = Gc::new(5);
        assert_eq!(*x.borrow(), 5);
    }

    #[test]
    fn test_simple_clone() {
        let x = Gc::new(5);
        let y = x.clone();
        assert_eq!(*x.borrow(), 5);
        assert_eq!(*y.borrow(), 5);
    }

    #[test]
    fn test_ptr_eq() {
        let x = Gc::new(5);
        let y = x.clone();
        let z = Gc::new(7);
        assert!(x.ptr_eq(&x));
        assert!(x.ptr_eq(&y));
        assert!(!x.ptr_eq(&z));
    }

    #[test]
    fn test_destructor() {
        let x = Gc::new(~5);
        assert_eq!(**x.borrow(), 5);
    }
}
