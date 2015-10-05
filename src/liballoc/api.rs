// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![unstable(feature = "allocator_api",
            reason = "the precise API and guarantees it provides may be tweaked \
                      slightly, especially to possibly take into account the \
                      types being stored to make room for a future \
                      tracing garbage collector",
            issue = "27700")]

use core::cmp;
use core::mem;
use core::nonzero::NonZero;
use core::ptr::{self, Unique};

pub type Size = NonZero<usize>;
pub type Capacity = NonZero<usize>;
pub type Alignment = usize;

pub type Address = NonZero<*mut u8>;

/// Represents the combination of a starting address and
/// a total capacity of the returned block.
pub struct Excess(Address, Capacity);

/// Category for a memory record.
///
/// An instance of `Kind` describes a particular layout of memory.
/// You build a `Kind` up as an input to give to an allocator.
///
/// All kinds have an associated positive size; note that this implies
/// zero-sized types have no corresponding kind.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Kind {
    size: Size,
    align: Alignment,
}

// Accessor methods
impl Kind {
    /// Returns size of the requested block of memory, measured in bytes.
    ///
    /// Returned size is guaranteed to be positive.
    pub fn size(&self) -> usize { *self.size }

    /// Returns alignment of the requested block of memory, measured in bytes.
    pub fn align(&self) -> usize { self.align }
}

fn size_align<T>() -> (usize, usize) {
    (mem::size_of::<T>(), mem::align_of::<T>())
}

impl Kind {
    fn from_size_align(size: usize, align: usize) -> Kind {
        let size = unsafe { assert!(size > 0); NonZero::new(size) };
        Kind { size: size, align: align }
    }
}

// FIXME: audit for overflow errors, (potentially switching to
// overflowing_add and overflowing_mul as necessary).

// public constructor methods
impl Kind {
    /// Creates a `Kind` describing the record for a single instance of `T`.
    /// Requires `T` has non-zero size.
    pub fn new<T>() -> Kind {
        let (size, align) = size_align::<T>();
        Kind::from_size_align(size, align)
    }

    /// Produces the `Kind` describing a record that could be used to
    /// allocate the backing structure for `T`, which could be a trait
    /// or other unsized type.
    ///
    /// Returns `None` if there is no backing memory for `*t`, e.g. if
    /// the size of the backing structure for `*t` has zero size.
    pub unsafe fn for_value<T: ?Sized>(t: &T) -> Option<Kind> {
        let (size, align) = (mem::size_of_val(t), mem::align_of_val(t));
        if size > 0 {
            Some(Kind::from_size_align(size, align))
        } else {
            None
        }
    }

    /// Creates a `Kind` describing the record that can hold a value
    /// of the same kind as `self`, but that also is aligned to
    /// alignment `align` (measured in bytes).
    ///
    /// Behavior undefined if `align` is not a power-of-two.
    ///
    /// If `self` already meets the prescribed alignment, then returns
    /// `self`.
    ///
    /// Note that this method does not add any padding to the overall
    /// size, regardless of whether the returned kind has a different
    /// alignment. You should be able to get that effect by passing
    /// an appropriately aligned zero-sized type to `Kind::extend`.
    pub fn align_to(self, align: Alignment) -> Kind {
        if align > self.align {
            Kind { align: align, ..self }
        } else {
            self
        }
    }

    /// Returns the amount of padding we must insert after `self`
    /// to ensure that the following address will satisfy `align`
    /// (measured in bytes).
    ///
    /// Behavior undefined if `align` is not a power-of-two.
    ///
    /// Note that for this to make sense, `align <= self.align`
    /// otherwise, the amount of inserted padding would need to depend
    /// on the particular starting address for the whole record.
    fn pad_to(self, align: Alignment) -> usize {
        debug_assert!(align <= self.align);
        let len = self.size();
        let len_rounded_up = (len + align - 1) & !(align - 1);
        return len_rounded_up - len;
    }

    /// Creates a `Kind` describing the record for `self` followed by
    /// `next`, including any necessary padding to ensure that `next`
    /// will be properly aligned. Note that the result `Kind` will
    /// satisfy the alignment properties of both `self` and `next`.
    ///
    /// Returns `(k, offset)`, where `k` is kind of the concatenated
    /// record and `offset` is the relative location, in bytes, of the
    /// start of the `next` embedded witnin the concatenated record
    /// (assuming that the record itself starts at offset 0).
    pub fn extend(self, next: Kind) -> (Kind, usize) {
        let new_align = cmp::max(self.align, next.align);
        let realigned = Kind { align: new_align, ..self };
        let pad = realigned.pad_to(new_align);
        let offset = self.size() + pad;
        let new_size = offset + next.size();
        (Kind::from_size_align(new_size, new_align), offset)
    }

    /// Creates a `Kind` describing the record for `n` instances of
    /// `self`, with a suitable amount of padding between each.
    ///
    /// Requires n > 0.
    pub fn array(self, n: usize) -> Kind {
        let padded_size = *self.size + self.pad_to(self.align);
        Kind::from_size_align(padded_size * n, self.align)
    }

    /// Creates a `Kind` describing the record for `n` instances of
    /// `self`, with no padding between each instance.
    ///
    /// Requires n > 0.
    pub fn array_packed(self, n: usize) -> Kind {
        let scaled = self.size() * n;
        let size = unsafe { assert!(scaled > 0); NonZero::new(scaled) };
        Kind { size: size, align: self.align }
    }

    /// Creates a `Kind` describing the record for `self` followed by
    /// `next` with no additional padding between the two. Since no
    /// padding is inserted, the alignment of `next` is irrelevant,
    /// and is not incoporated *at all* into the resulting `Kind`.
    ///
    /// Returns `(k, offset)`, where `k` is kind of the concatenated
    /// record and `offset` is the relative location, in bytes, of the
    /// start of the `next` embedded witnin the concatenated record
    /// (assuming that the record itself starts at offset 0).
    ///
    /// (The `offset` is always the same as `self.size()`; we use this
    ///  signature out of convenience in matching the signature of
    ///  `Kind::extend`.)
    pub fn extend_packed(self, next: Kind) -> (Kind, usize) {
        let new_size = unsafe { NonZero::new(self.size() + next.size()) };
        (Kind { size: new_size, ..self }, self.size())
    }
}

/// Allocation failures provide feedback about the cause of the error.
pub trait AllocError {
    /// Returns true if the error is due to hitting some resource
    /// limit or otherwise running out of memory. This condition
    /// strongly implies that some series of deallocations will allow
    /// a subsequent reissuing of the original allocation request to
    /// succeed.
    ///
    /// This is the usual interpretation of an allocation failure;
    /// e.g. usually when `malloc` returns `null`, it is because of
    /// hitting a user resource limit or system memory exhaustion.
    ///
    /// Note that the resource exhaustion could be specific to the
    /// original allocator (i.e. the only way to free up memory is by
    /// deallocating memory attached to that allocator) or it could
    /// be associated with some other state outside of the original
    /// alloactor.
    fn is_memory_exhausted(&self) -> bool;

    /// Returns true if the allocator is fundamentally incapable of
    /// satisfying the original request. This condition implies that
    /// such an allocation request will ever succeed on this
    /// allocator, regardless of environment, memory pressure, or
    /// other contextual condtions.
    ///
    /// An example where this might arise: A block allocator that only
    /// supports satisfying memory requests where each allocated block
    /// is at most K bytes in size.
    fn is_request_unsupported(&self) -> bool;
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct MemoryExhausted;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum AllocErr {
    Exhausted,
    Unsupported,
}

impl AllocError for MemoryExhausted {
    fn is_memory_exhausted(&self) -> bool { true }
    fn is_request_unsupported(&self) -> bool { false }
}

impl AllocError for AllocErr {
    fn is_memory_exhausted(&self) -> bool { *self == AllocErr::Exhausted }
    fn is_request_unsupported(&self) -> bool { *self == AllocErr::Unsupported }
}

/// An implementation of `Allocator` can allocate, reallocate, and
/// deallocate arbitrary blocks of data described via `Kind`.
///
/// Some of the methods require that a kind *fit* a memory block.
/// What it means for a kind to "fit" a memory block means is that
/// the following two conditions must hold:
///
/// 1. The block's starting address must be aligned to `kind.align()`.
///
/// 2. The block's size must fall in the range `[orig, usable]`, where:
///
///    * `orig` is the size last used to allocate the block, and
///
///    * `usable` is the capacity that was (or would have been)
///      returned when (if) the block was allocated via a call to
///      `alloc_excess` or `realloc_excess`.
///
/// Note that due to the constraints in the methods below, a
/// lower-bound on `usable` can be safely approximated by a call to
/// `usable_size`.
pub trait Allocator {
    /// When allocation requests cannot be satisified, an instance of
    /// this error is returned.
    ///
    /// Many allocators will want to use the zero-sized
    /// `MemoryExhausted` type for this.
    type Error: AllocError;

    /// Returns a pointer suitable for holding data described by
    /// `kind`, meeting its size and alignment guarantees.
    ///
    /// The returned block of storage may or may not be initialized.
    /// (Extension subtraits might restrict this, e.g. to ensure
    /// initialization.)
    ///
    /// Behavior undefined if `kind.size()` is 0 or if `kind.align()`
    /// is larger than the largest platform-supported page size.
    unsafe fn alloc(&mut self, kind: Kind) -> Result<Address, Self::Error>;

    /// Deallocate the memory referenced by `ptr`.
    ///
    /// `ptr` must have previously been provided via this allocator,
    /// and `kind` must *fit* the provided block.
    unsafe fn dealloc(&mut self, ptr: Address, kind: Kind);

    /// Returns the minimum guaranteed usable size of a successful
    /// allocation created with the specified `kind`.
    ///
    /// Clients who wish to make use of excess capacity are encouraged
    /// to use the `alloc_excess` and `realloc_excess` instead, as
    /// this method is constrained to conservatively report a value
    /// less than or equal to the minimum capacity for *all possible*
    /// calls to those methods.
    ///
    /// However, for clients that do not wish to track the capacity
    /// returned by `alloc_excess` locally, this method is likely to
    /// produce useful results.
    unsafe fn usable_size(&self, kind: Kind) -> Capacity { kind.size }

    /// Extends or shrinks the allocation referenced by `ptr` to
    /// `new_size` bytes of memory, retaining the alignment `align`
    /// and value-tracking state specified by `kind`.
    ///
    /// `ptr` must have previously been provided via this allocator.
    ///
    /// `kind` must *fit* the `ptr` (see above).
    ///
    /// If this returns non-null, then the memory block referenced by
    /// `ptr` may have been freed and should be considered unusable.
    ///
    /// Returns null if allocation fails; in this scenario, the
    /// original memory block referenced by `ptr` is unaltered.
    ///
    /// Behavior undefined if above constraints are unmet. Behavior
    /// also undefined if `new_size` is 0.
    unsafe fn realloc(&mut self, ptr: Address, kind: Kind, new_size: Size) -> Result<Address, Self::Error> {
        if new_size <= self.usable_size(kind) {
            return Ok(ptr);
        } else {
            let result = self.alloc(Kind { size: new_size, ..kind });
            if let Ok(new_ptr) = result {
                ptr::copy(*ptr as *const u8, *new_ptr, cmp::min(kind.size(), *new_size));
                self.dealloc(ptr, kind);
            }
            result
        }
    }

    /// Behaves like `fn alloc`, but also returns the whole size of
    /// the returned block. For some `kind` inputs, like arrays, this
    /// may include extra storage usable for additional data.
    unsafe fn alloc_excess(&mut self, kind: Kind) -> Result<Excess, Self::Error> {
        self.alloc(kind).map(|p| Excess(p, self.usable_size(kind)))
    }

    /// Behaves like `fn realloc`, but also returns the whole size of
    /// the returned block. For some `kind` inputs, like arrays, this
    /// may include extra storage usable for additional data.
    unsafe fn realloc_excess(&mut self,
                             ptr: Address,
                             kind: Kind,
                             new_size: Size) -> Result<Excess, Self::Error> {
        self.realloc(ptr, kind, new_size)
            .map(|p| Excess(p, self.usable_size(Kind { size: new_size, ..kind })))
    }

    /// Allocates a block suitable for holding an instance of `T`.
    ///
    /// Captures a common usage pattern for allocators.
    unsafe fn alloc_one<T>(&mut self) -> Result<Unique<T>, Self::Error> {
        self.alloc(Kind::new::<T>())
            .map(|p|Unique::new(*p as *mut T))
    }

    /// Deallocates a block suitable for holding an instance of `T`.
    ///
    /// Captures a common usage pattern for allocators.
    unsafe fn dealloc_one<T>(&mut self, mut ptr: Unique<T>) {
        let raw_ptr = NonZero::new(ptr.get_mut() as *mut T as *mut u8);
        self.dealloc(raw_ptr, Kind::new::<T>());
    }

    /// Allocates a block suitable for holding `n` instances of `T`.
    ///
    /// Captures a common usage pattern for allocators.
    unsafe fn alloc_array<T>(&mut self, n: usize) -> Result<Unique<T>, Self::Error> {
        self.alloc(Kind::new::<T>().array(n))
            .map(|p|Unique::new(*p as *mut T))
    }

    /// Deallocates a block suitable for holding `n` instances of `T`.
    ///
    /// Captures a common usage pattern for allocators.
    unsafe fn dealloc_array<T>(&mut self, ptr: Unique<T>, n: usize) {
        let raw_ptr = NonZero::new(*ptr as *mut u8);
        self.dealloc(raw_ptr, Kind::new::<T>().array(n));
    }

    /// Allocator-specific method for signalling an out-of-memory
    /// condition.
    ///
    /// Any activity done by the `oom` method must not allocate
    /// from `self` (otherwise you essentially infinite regress).
    unsafe fn oom(&mut self) -> ! { ::core::intrinsics::abort() }
}
