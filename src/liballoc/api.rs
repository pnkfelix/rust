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
pub type Alignment = NonZero<usize>;

pub type Address = NonZero<*mut u8>;

/// Represents the combination of a starting address and
/// a total capacity of the returned block.
pub struct Excess(Address, Capacity);

pub trait AllocKind: Sized {
    /// Returns size of the requested block of memory, measured in bytes.
    fn size(&self) -> NonZero<usize>;

    /// Returns alignment of the requested block of memory, measured in bytes.
    fn align(&self) -> NonZero<usize>;

    /// Creates kind describing the record for a single instance of `T`.
    /// Requires `T` has non-zero size.
    fn new<T>() -> Self;

    /// Produces kind describing a record that could be used to
    /// allocate the backing structure for `T`, which could be a trait
    /// or other unsized type.
    ///
    /// Returns `None` if there is no backing memory for `*t`, e.g. if
    /// the size of the backing structure for `*t` has zero size.
    unsafe fn for_value<T: ?Sized>(t: &T) -> Option<Self>;

    /// Creates a kind describing the record that can hold a value of
    /// the same kind as `self` except with size `new_size` bytes.
    fn resize(&self, new_size: Size) -> Self;

    /// Creates a kind describing the record that can hold a value
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
    /// an appropriately aligned zero-sized type to `fn extend`.
    fn align_to(&self, align: Alignment) -> Self;

    /// Returns the amount of padding we must insert after `self`
    /// to ensure that the following address will satisfy `align`
    /// (measured in bytes).
    ///
    /// Behavior undefined if `align` is not a power-of-two.
    ///
    /// Note that for this to make sense, `align <= self.align`
    /// otherwise, the amount of inserted padding would need to depend
    /// on the particular starting address for the whole record.
    fn pad_to(&self, align: Alignment) -> usize {
        debug_assert!(*align <= *self.align());
        let len = *self.size();
        let len_rounded_up = (len + *align - 1) & !(*align - 1);
        return len_rounded_up - len;
    }

    /// Creates a kind describing the record for `self` followed by
    /// `next`, including any necessary padding to ensure that `next`
    /// will be properly aligned. Note that the result kind will
    /// satisfy the alignment properties of both `self` and `next`.
    ///
    /// Returns `Some((k, offset))`, where `k` is kind of the concatenated
    /// record and `offset` is the relative location, in bytes, of the
    /// start of the `next` embedded witnin the concatenated record
    /// (assuming that the record itself starts at offset 0).
    ///
    /// On arithmetic overflow, returns `None`.
    fn extend(&self, next: Self) -> Option<(Self, usize)>;

    /// Creates a kind describing the record for `n` instances of
    /// `self`, with a suitable amount of padding between each.
    ///
    /// On zero `n` or arithmetic overflow, returns `None`.
    fn array(&self, n: usize) -> Option<Self>;

    /// Creates a kind describing the record for `n` instances of
    /// `self`, with no padding between each instance.
    ///
    /// On zero `n` or overflow, returns `None`.
    fn array_packed(&self, n: usize) -> Option<Self>;

    /// Creates a kind describing the record for `self` followed by
    /// `next` with no additional padding between the two. Since no
    /// padding is inserted, the alignment of `next` is irrelevant,
    /// and is not incoporated *at all* into the resulting kind.
    ///
    /// Returns `(k, offset)`, where `k` is kind of the concatenated
    /// record and `offset` is the relative location, in bytes, of the
    /// start of the `next` embedded witnin the concatenated record
    /// (assuming that the record itself starts at offset 0).
    ///
    /// (The `offset` is always the same as `self.size()`; we use this
    ///  signature out of convenience in matching the signature of
    ///  `fn extend`.)
    ///
    /// On arithmetic overflow, returns `None`.
    fn extend_packed(&self, next: Self) -> Option<(Self, usize)>;

    // Below family of methods *assume* inputs are pre- or
    // post-validated in some manner; thus `AllocKind` impls may override
    // them with variants that bypass the slower checked arithmetic
    // operations.
    //
    // (Note that the default implementations do end up checking that
    // the preconditions are satisfied, but that is *not* required by
    // the specification of the methods. That is merely a convenience
    // operating under the assumption that most allocator clients will
    // *not* use the below methods and thus most Allocator
    // implementations need not implement fast-paths for them.)

    /// Creates a kind describing the record for `self` followed by
    /// `next`, including any necessary padding to ensure that `next`
    /// will be properly aligned. Note that the result kind will
    /// satisfy the alignment properties of both `self` and `next`.
    ///
    /// Returns `(k, offset)`, where `k` is kind of the concatenated
    /// record and `offset` is the relative location, in bytes, of the
    /// start of the `next` embedded witnin the concatenated record
    /// (assuming that the record itself starts at offset 0).
    ///
    /// Requires no arithmetic overflow from inputs.
    unsafe fn extend_unchecked(&self, next: Self) -> (Self, usize) {
        self.extend(next).unwrap()
    }

    /// Creates a kind describing the record for `n` instances of
    /// `self`, with a suitable amount of padding between each.
    ///
    /// Requires non-zero `n` and no arithmetic overflow from inputs.
    /// (See also the `fn array` checked variant.)
    unsafe fn array_unchecked(&self, n: usize) -> Self {
        self.array(n).unwrap()
    }

    /// Creates a kind describing the record for `n` instances of
    /// `self`, with no padding between each instance.
    ///
    /// Requires non-zero `n` and no arithmetic overflow from inputs.
    /// (See also the `fn array_packed` checked variant.)
    unsafe fn array_packed_unchecked(&self, n: usize) -> Self {
        self.array_packed(n).unwrap()
    }

    /// Creates a kind describing the record for `self` followed by
    /// `next` with no additional padding between the two. Since no
    /// padding is inserted, the alignment of `next` is irrelevant,
    /// and is not incoporated *at all* into the resulting kind.
    ///
    /// Returns `(k, offset)`, where `k` is kind of the concatenated
    /// record and `offset` is the relative location, in bytes, of the
    /// start of the `next` embedded witnin the concatenated record
    /// (assuming that the record itself starts at offset 0).
    ///
    /// (The `offset` is always the same as `self.size()`; we use this
    ///  signature out of convenience in matching the signature of
    ///  `fn extend`.)
    ///
    /// Requires no arithmetic overflow from inputs.
    /// (See also the `fn extend_packed` checked variant.)
    unsafe fn extend_packed_unchecked(&self, next: Self) -> (Self, usize) {
        self.extend_packed(next).unwrap()
    }
}

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

fn size_align<T>() -> (usize, usize) {
    (mem::size_of::<T>(), mem::align_of::<T>())
}

impl Kind {
    fn from_size_align(size: usize, align: usize) -> Kind {
        let size = unsafe { assert!(size > 0); NonZero::new(size) };
        let align = unsafe { assert!(align > 0); NonZero::new(align) };
        Kind { size: size, align: align }
    }
}

// FIXME: audit for overflow errors, (potentially switching to
// overflowing_add and overflowing_mul as necessary).

impl AllocKind for Kind {
    // Accessor methods

    fn size(&self) -> NonZero<usize> { self.size }

    fn align(&self) -> NonZero<usize> { self.align }

    // public constructor methods

    fn new<T>() -> Kind {
        let (size, align) = size_align::<T>();
        Kind::from_size_align(size, align)
    }

    unsafe fn for_value<T: ?Sized>(t: &T) -> Option<Kind> {
        let (size, align) = (mem::size_of_val(t), mem::align_of_val(t));
        if size > 0 {
            Some(Kind::from_size_align(size, align))
        } else {
            None
        }
    }

    fn resize(&self, new_size: Size) -> Kind {
        Kind { size: new_size, ..*self }
    }

    fn align_to(&self, align: Alignment) -> Kind {
        if align > self.align {
            Kind { align: align, ..*self }
        } else {
            *self
        }
    }

    fn extend(&self, next: Self) -> Option<(Kind, usize)> {
        let new_align = unsafe { NonZero::new(cmp::max(*self.align, *next.align)) };
        let realigned = Kind { align: new_align, ..*self };
        let pad = realigned.pad_to(new_align);
        let offset = *self.size() + pad;
        let new_size = offset + *next.size();
        Some((Kind::from_size_align(new_size, *new_align), offset))
    }

    fn array(&self, n: usize) -> Option<Kind> {
        let padded_size = match self.size.checked_add(self.pad_to(self.align)) {
            None => return None,
            Some(padded_size) => padded_size,
        };
        let alloc_size = match padded_size.checked_mul(n) {
            None => return None,
            Some(alloc_size) => alloc_size,
        };
        Some(Kind::from_size_align(alloc_size, *self.align))
    }

    fn array_packed(&self, n: usize) -> Option<Kind> {
        let scaled = match self.size().checked_mul(n) {
            None => return None,
            Some(scaled) => scaled,
        };
        let size = unsafe { assert!(scaled > 0); NonZero::new(scaled) };
        Some(Kind { size: size, align: self.align })
    }

    fn extend_packed(&self, next: Self) -> Option<(Self, usize)> {
        let new_size = match self.size().checked_add(*next.size()) {
            None => return None,
            Some(new_size) => new_size,
        };
        let new_size = unsafe { NonZero::new(new_size) };
        Some((Kind { size: new_size, ..*self }, *self.size()))
    }
}

/// Allocation failures provide feedback about the cause of the error.
pub trait AllocError {
    /// Construct an error that indicates operation failure due to
    /// invalid input values for the request.
    ///
    /// This is used for example to indicate that an overflow occurred
    /// during arithmetic computation. (However, since generally
    /// overflows represent allocation attempt that would exhaust
    /// memory, clients are alternatively allowed to constuct an error
    /// representing memory exhaustion.)
    fn invalid_input() -> Self;

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
pub struct RequestUnsupported;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum AllocErr {
    Exhausted,
    Unsupported,
}

impl AllocError for MemoryExhausted {
    fn invalid_input() -> Self { MemoryExhausted }
    fn is_memory_exhausted(&self) -> bool { true }
    fn is_request_unsupported(&self) -> bool { false }
}

impl AllocError for AllocErr {
    fn invalid_input() -> Self { AllocErr::Unsupported }
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
    /// Describes the sort of records that this allocator can
    /// construct.
    type Kind: AllocKind;

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
    unsafe fn alloc(&mut self, kind: &Self::Kind) -> Result<Address, Self::Error>;

    /// Deallocate the memory referenced by `ptr`.
    ///
    /// `ptr` must have previously been provided via this allocator,
    /// and `kind` must *fit* the provided block.
    unsafe fn dealloc(&mut self, ptr: Address, kind: &Self::Kind);

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
    unsafe fn usable_size(&self, kind: &Self::Kind) -> Capacity { kind.size() }

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
    unsafe fn realloc(&mut self, ptr: Address, kind: &Self::Kind, new_size: Size) -> Result<Address, Self::Error> {
        if new_size <= self.usable_size(kind) {
            return Ok(ptr);
        } else {
            let result = self.alloc(&kind.resize(new_size));
            if let Ok(new_ptr) = result {
                ptr::copy(*ptr as *const u8, *new_ptr, cmp::min(*kind.size(), *new_size));
                self.dealloc(ptr, kind);
            }
            result
        }
    }

    /// Behaves like `fn alloc`, but also returns the whole size of
    /// the returned block. For some `kind` inputs, like arrays, this
    /// may include extra storage usable for additional data.
    unsafe fn alloc_excess(&mut self, kind: &Self::Kind) -> Result<Excess, Self::Error> {
        self.alloc(kind).map(|p| Excess(p, self.usable_size(kind)))
    }

    /// Behaves like `fn realloc`, but also returns the whole size of
    /// the returned block. For some `kind` inputs, like arrays, this
    /// may include extra storage usable for additional data.
    unsafe fn realloc_excess(&mut self,
                             ptr: Address,
                             kind: &Self::Kind,
                             new_size: Size) -> Result<Excess, Self::Error> {
        self.realloc(ptr, kind, new_size)
            .map(|p| Excess(p, self.usable_size(&kind.resize(new_size))))
    }

    /// Allocates a block suitable for holding an instance of `T`.
    ///
    /// Captures a common usage pattern for allocators.
    unsafe fn alloc_one<T>(&mut self) -> Result<Unique<T>, Self::Error> {
        self.alloc(&Self::Kind::new::<T>())
            .map(|p|Unique::new(*p as *mut T))
    }

    /// Deallocates a block suitable for holding an instance of `T`.
    ///
    /// Captures a common usage pattern for allocators.
    unsafe fn dealloc_one<T>(&mut self, mut ptr: Unique<T>) {
        let raw_ptr = NonZero::new(ptr.get_mut() as *mut T as *mut u8);
        self.dealloc(raw_ptr, &Self::Kind::new::<T>());
    }

    /// Allocates a block suitable for holding `n` instances of `T`.
    ///
    /// Captures a common usage pattern for allocators.
    unsafe fn alloc_array<T>(&mut self, n: usize) -> Result<Unique<T>, Self::Error> {
        match Self::Kind::new::<T>().array(n) {
            Some(kind) => self.alloc(&kind).map(|p|Unique::new(*p as *mut T)),
            None => Err(Self::Error::invalid_input()),
        }
    }

    /// Deallocates a block suitable for holding `n` instances of `T`.
    ///
    /// Captures a common usage pattern for allocators.
    unsafe fn dealloc_array<T>(&mut self, ptr: Unique<T>, n: usize) {
        let raw_ptr = NonZero::new(*ptr as *mut u8);
        self.dealloc(raw_ptr, &Self::Kind::new::<T>().array(n).unwrap());
    }

    /// Allocates a block suitable for holding `n` instances of `T`.
    ///
    /// Captures a common usage pattern for allocators.
    ///
    /// Requires inputs are non-zero and do not cause arithmetic overflow.
    unsafe fn alloc_array_unchecked<T>(&mut self, n: usize) -> Result<Unique<T>, Self::Error> {
        let kind = Self::Kind::new::<T>().array_unchecked(n);
        self.alloc(&kind).map(|p|Unique::new(*p as *mut T))
    }

    /// Deallocates a block suitable for holding `n` instances of `T`.
    ///
    /// Captures a common usage pattern for allocators.
    ///
    /// Requires inputs are non-zero and do not overflow.
    unsafe fn dealloc_array_unchecked<T>(&mut self, ptr: Unique<T>, n: usize) {
        let kind = Self::Kind::new::<T>().array_unchecked(n);
        self.dealloc(NonZero::new(*ptr as *mut u8), &kind);
    }

    /// Allocator-specific method for signalling an out-of-memory
    /// condition.
    ///
    /// Any activity done by the `oom` method must not allocate
    /// from `self` (otherwise you essentially infinite regress).
    unsafe fn oom(&mut self) -> ! { ::core::intrinsics::abort() }
}
