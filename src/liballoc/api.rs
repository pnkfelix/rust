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
use core::fmt;
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

/// Category for a memory record.
///
/// An instance of `Kind` describes a particular layout of memory.
/// You build a `Kind` up as an input to give to an allocator.
///
/// All kinds have an associated positive size; note that this implies
/// zero-sized types have no corresponding kind.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Kind {
    // size of the requested block of memory, measured in bytes.
    size: Size,
    // alignment of the requested block of memory, measured in bytes.
    // we ensure that this is always a power-of-two, because API's
    ///like `posix_memalign` require it and it is a reasonable
    // constraint to impose on Kind constructors.
    //
    // (However, we do not analogously require `align >= sizeof(void*)`,
    //  even though that is *also* a requirement of `posix_memalign`.)
    align: Alignment,
}


// FIXME: audit for overflow errors, (potentially switching to
// overflowing_add and overflowing_mul as necessary).

impl Kind {
    // (private constructor)
    fn from_size_align(size: usize, align: usize) -> Kind {
        assert!(align.is_power_of_two()); 
        let size = unsafe { assert!(size > 0); NonZero::new(size) };
        let align = unsafe { assert!(align > 0); NonZero::new(align) };
        Kind { size: size, align: align }
    }

    /// The minimum size in bytes for a memory block of this kind.
    pub fn size(&self) -> NonZero<usize> { self.size }

    /// The minimum byte alignment for a memory block of this kind.
    pub fn align(&self) -> NonZero<usize> { self.align }

    /// Constructs a `Kind` suitable for holding a value of type `T`.
    /// Returns `None` if no such kind exists (e.g. for zero-sized `T`).
    pub fn new<T>() -> Option<Self> {
        let (size, align) = size_align::<T>();
        if size > 0 { Some(Kind::from_size_align(size, align)) } else { None }
    }

    /// Produces kind describing a record that could be used to
    /// allocate backing structure for `T` (which could be a trait
    /// or other unsized type like a slice).
    ///
    /// Returns `None` when no such kind exists; for example, when `x`
    /// is a reference to a zero-sized type.
    pub fn for_value<T: ?Sized>(t: &T) -> Option<Self> {
        let (size, align) = (mem::size_of_val(t), mem::align_of_val(t));
        if size > 0 {
            Some(Kind::from_size_align(size, align))
        } else {
            None
        }
    }

    /// Creates a kind describing the record that can hold a value
    /// of the same kind as `self`, but that also is aligned to
    /// alignment `align` (measured in bytes).
    ///
    /// If `self` already meets the prescribed alignment, then returns
    /// `self`.
    ///
    /// Note that this method does not add any padding to the overall
    /// size, regardless of whether the returned kind has a different
    /// alignment. In other words, if `K` has size 16, `K.align_to(32)`
    /// will *still* have size 16.
    pub fn align_to(&self, align: Alignment) -> Self {
        if align > self.align {
            let pow2_align = align.checked_next_power_of_two().unwrap();
            debug_assert!(pow2_align > 0); // (this follows from self.align > 0...)
            Kind { align: unsafe { NonZero::new(pow2_align) },
                   ..*self }
        } else {
            *self
        }
    }

    /// Returns the amount of padding we must insert after `self`
    /// to ensure that the following address will satisfy `align`
    /// (measured in bytes).
    ///
    /// Behavior undefined if `align` is not a power-of-two.
    ///
    /// Note that in practice, this is only useable if `align <=
    /// self.align` otherwise, the amount of inserted padding would
    /// need to depend on the particular starting address for the
    /// whole record, because `self.align` would not provide
    /// sufficient constraint.
    pub fn padding_needed_for(&self, align: Alignment) -> usize {
        debug_assert!(*align <= *self.align());
        let len = *self.size();
        let len_rounded_up = (len + *align - 1) & !(*align - 1);
        return len_rounded_up - len;
    }

    /// Creates a kind describing the record for `n` instances of
    /// `self`, with a suitable amount of padding between each to
    /// ensure that each instance is given its requested size and
    /// alignment. On success, returns `(k, offs)` where `k` is the
    /// kind of the array and `offs` is the distance between the start
    /// of each element in the array.
    ///
    /// On zero `n` or arithmetic overflow, returns `None`.
    pub fn repeat(&self, n: usize) -> Option<(Self, usize)> {
        if n == 0 { return None; }
        let padded_size = match self.size.checked_add(self.padding_needed_for(self.align)) {
            None => return None,
            Some(padded_size) => padded_size,
        };
        let alloc_size = match padded_size.checked_mul(n) {
            None => return None,
            Some(alloc_size) => alloc_size,
        };
        Some((Kind::from_size_align(alloc_size, *self.align), padded_size))
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
    pub fn extend(&self, next: Self) -> Option<(Self, usize)> {
        let new_align = unsafe { NonZero::new(cmp::max(*self.align, *next.align)) };
        let realigned = Kind { align: new_align, ..*self };
        let pad = realigned.padding_needed_for(new_align);
        let offset = *self.size() + pad;
        let new_size = offset + *next.size();
        Some((Kind::from_size_align(new_size, *new_align), offset))
    }

    /// Creates a kind describing the record for `n` instances of
    /// `self`, with no padding between each instance.
    ///
    /// On zero `n` or overflow, returns `None`.
    pub fn repeat_packed(&self, n: usize) -> Option<Self> {
        let scaled = match self.size().checked_mul(n) {
            None => return None,
            Some(scaled) => scaled,
        };
        let size = unsafe { assert!(scaled > 0); NonZero::new(scaled) };
        Some(Kind { size: size, align: self.align })
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
    /// On arithmetic overflow, returns `None`.
    pub fn extend_packed(&self, next: Self) -> Option<(Self, usize)> {
        let new_size = match self.size().checked_add(*next.size()) {
            None => return None,
            Some(new_size) => new_size,
        };
        let new_size = unsafe { NonZero::new(new_size) };
        Some((Kind { size: new_size, ..*self }, *self.size()))
    }

    // Below family of methods *assume* inputs are pre- or
    // post-validated in some manner. (The implementations here
    ///do indirectly validate, but that is not part of their
    /// specification.)
    //
    // Since invalid inputs could yield ill-formed kinds, these
    // methods are `unsafe`.

    /// Creates kind describing the record for a single instance of `T`.
    /// Requires `T` has non-zero size.
    pub unsafe fn new_unchecked<T>() -> Self {
        let (size, align) = size_align::<T>();
        Kind::from_size_align(size, align)
    }


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
    pub unsafe fn extend_unchecked(&self, next: Self) -> (Self, usize) {
        self.extend(next).unwrap()
    }

    /// Creates a kind describing the record for `n` instances of
    /// `self`, with a suitable amount of padding between each.
    ///
    /// Requires non-zero `n` and no arithmetic overflow from inputs.
    /// (See also the `fn array` checked variant.)
    pub unsafe fn repeat_unchecked(&self, n: usize) -> (Self, usize) {
        self.repeat(n).unwrap()
    }

    /// Creates a kind describing the record for `n` instances of
    /// `self`, with no padding between each instance.
    ///
    /// Requires non-zero `n` and no arithmetic overflow from inputs.
    /// (See also the `fn array_packed` checked variant.)
    pub unsafe fn repeat_packed_unchecked(&self, n: usize) -> Self {
        self.repeat_packed(n).unwrap()
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
    pub unsafe fn extend_packed_unchecked(&self, next: Self) -> (Self, usize) {
        self.extend_packed(next).unwrap()
    }

    /// Creates a kind describing the record for a `[T; n]`.
    ///
    /// On zero `n`, zero-sized `T`, or arithmetic overflow, returns `None`.
    pub fn array<T>(n: usize) -> Option<Self> {
        Kind::new::<T>()
            .and_then(|k| k.repeat(n))
            .map(|(k, offs)| {
                debug_assert!(offs == mem::size_of::<T>());
                k
            })
    }

    /// Creates a kind describing the record for a `[T; n]`.
    ///
    /// Requires nonzero `n`, nonzero-sized `T`, and no arithmetic
    /// overflow; otherwise behavior undefined.
    pub fn array_unchecked<T>(n: usize) -> Self {
        Kind::array::<T>(n).unwrap()
    }

}

fn size_align<T>() -> (usize, usize) {
    (mem::size_of::<T>(), mem::align_of::<T>())
}

/// `AllocError` instances provide feedback about the cause of an allocation failure.
pub trait AllocError {
    /// Construct an error that indicates operation failure due to
    /// invalid input values for the request.
    ///
    /// This can be used, for example, to signal an overflow occurred
    /// during arithmetic computation. (However, since overflows
    /// frequently represent an allocation attempt that would exhaust
    /// memory, clients are alternatively allowed to constuct an error
    /// representing memory exhaustion in such scenarios.)
    fn invalid_input() -> Self;

    /// Returns true if the error is due to hitting some resource
    /// limit or otherwise running out of memory. This condition
    /// strongly implies that *some* series of deallocations would
    /// allow a subsequent reissuing of the original allocation
    /// request to succeed.
    ///
    /// Exhaustion is a common interpretation of an allocation failure;
    /// e.g. usually when `malloc` returns `null`, it is because of
    /// hitting a user resource limit or system memory exhaustion.
    ///
    /// Note that the resource exhaustion could be specific to the
    /// original allocator (i.e. the only way to free up memory is by
    /// deallocating memory attached to that allocator), or it could
    /// be associated with some other state outside of the original
    /// alloactor. The `AllocError` trait does not distinguish between
    /// the two scenarios.
    ///
    /// Finally, error responses to allocation input requests that are
    /// *always* illegal for *any* allocator (e.g. zero-sized or
    /// arithmetic-overflowing requests) are allowed to respond `true`
    /// here. (This is to allow `MemoryExhausted` as a valid error type
    /// for an allocator that can handle all "sane" requests.)
    fn is_memory_exhausted(&self) -> bool;

    /// Returns true if the allocator is fundamentally incapable of
    /// satisfying the original request. This condition implies that
    /// such an allocation request will never succeed on this
    /// allocator, regardless of environment, memory pressure, or
    /// other contextual condtions.
    ///
    /// An example where this might arise: A block allocator that only
    /// supports satisfying memory requests where each allocated block
    /// is at most `K` bytes in size.
    fn is_request_unsupported(&self) -> bool;

    /// Returns true only if the error is transient. "Transient" is
    /// meant here in the sense that there is a reasonable chance that
    /// re-issuing the same allocation request in the future *could*
    /// succeed, even if nothing else changes about the overall
    /// context of the request.
    ///
    /// An example where this might arise: An allocator shared across
    /// threads that fails upon detecting interference (rather than
    /// e.g. blocking).
    fn is_transient(&self) -> bool { false } // most errors are not transient
}

/// The `MemoryExhausted` error represents a blanket condition
/// that the given request was not satisifed for some reason beyond
/// any particular limitations of a given allocator.
///
/// It roughly corresponds to getting `null` back from a call to `malloc`:
/// you've probably exhausted memory (though there might be some other
/// explanation; see discussion with `AllocError::is_memory_exhausted`).
///
/// Allocators that can in principle allocate any kind of legal input
/// might choose this as their associated error type.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct MemoryExhausted;

/// The `AllocErr` error specifies whether an allocation failure is
/// specifically due to resource exhaustion or if it is due to
/// something wrong when combining the given input arguments with this
/// allocator.

/// Allocators that only support certain classes of inputs might choose this
/// as their associated error type, so that clients can respond appropriately
/// to specific error failure scenarios.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum AllocErr {
    /// Error due to hitting some resource limit or otherwise running
    /// out of memory. This condition strongly implies that *some*
    /// series of deallocations would allow a subsequent reissuing of
    /// the original allocation request to succeed.
    Exhausted,

    /// Error due to allocator being fundamentally incapable of
    /// satisfying the original request. This condition implies that
    /// such an allocation request will never succeed on the given
    /// allocator, regardless of environment, memory pressure, or
    /// other contextual condtions.
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
pub unsafe trait Allocator {
    /// When allocation requests cannot be satisified, an instance of
    /// this error is returned.
    ///
    /// Many allocators will want to use the zero-sized
    /// `MemoryExhausted` type for this.
    type Error: AllocError + fmt::Debug;

    /// Returns a pointer suitable for holding data described by
    /// `kind`, meeting its size and alignment guarantees.
    ///
    /// The returned block of storage may or may not have its contents
    /// initialized. (Extension subtraits might restrict this
    /// behavior, e.g. to ensure initialization.)
    ///
    /// Returns `Err` if allocation fails or if `kind` does
    /// not meet allocator's size or alignment constraints.
    unsafe fn alloc(&mut self, kind: Kind) -> Result<Address, Self::Error>;

    /// Deallocate the memory referenced by `ptr`.
    ///
    /// `ptr` must have previously been provided via this allocator,
    /// and `kind` must *fit* the provided block (see above);
    /// otherwise yields undefined behavior.
    ///
    /// Returns `Err` only if deallocation fails in some fashion. If
    /// the returned error is *transient*, then ownership of the
    /// memory block is transferred back to the caller (see
    /// `AllocError::is_transient`). Otherwise, callers must assume
    /// that ownership of the block has been unrecoverably lost.
    ///
    /// Note: Implementors are encouraged to avoid `Err`-failure from
    /// `dealloc`; most memory allocation APIs do not support
    /// signalling failure in their `free` routines, and clients are
    /// likely to incorporate that assumption into their own code and
    /// just `unwrap` the result of this call.
    unsafe fn dealloc(&mut self, ptr: Address, kind: Kind) -> Result<(), Self::Error>;

    /// Allocator-specific method for signalling an out-of-memory
    /// condition.
    ///
    /// Any activity done by the `oom` method should ensure that it
    /// does not infinitely regress in nested calls to `oom`. In
    /// practice this means implementors should eschew allocating,
    /// especially from `self` (directly or indirectly).
    ///
    /// Implementors of this trait are discouraged from panicking or
    /// aborting from other methods in the event of memory exhaustion;
    /// instead they should return an appropriate error from the
    /// invoked method, and let the client decide whether to invoke
    /// this `oom` method.
    unsafe fn oom(&mut self) -> ! { ::core::intrinsics::abort() }

    // == ALLOCATOR-SPECIFIC QUANTITIES AND LIMITS ==
    // max_size, max_align, usable_size

    /// The maximum requestable size in bytes for memory blocks
    /// managed by this allocator.
    ///
    /// Returns `None` if this allocator has no explicit maximum size.
    /// (Note that such allocators may well still have an *implicit*
    /// maximum size; i.e. allocation requests can always fail.)
    fn max_size(&self) -> Option<Size> { None }

    /// The maximum requestable alignment in bytes for memory blocks
    /// managed by this allocator.
    ///
    /// Returns `None` if this allocator has no assigned maximum
    /// alignment.  (Note that such allocators may well still have an
    /// *implicit* maximum alignment; i.e. allocation requests can
    /// always fail.)
    fn max_align(&self) -> Option<Alignment> { None }

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
    unsafe fn usable_size(&self, kind: Kind) -> Capacity { kind.size() }

    // == METHODS FOR MEMORY REUSE ==
    // realloc. alloc_excess, realloc_excess
    
    /// Returns a pointer suitable for holding data described by
    /// `new_kind`, meeting its size and alignment guarantees. To
    /// accomplish this, this may extend or shrink the allocation
    /// referenced by `ptr` to fit `new_kind`.
    ///
    /// * `ptr` must have previously been provided via this allocator.
    ///
    /// * `kind` must *fit* the `ptr` (see above). (The `new_kind`
    ///   argument need not fit it.)
    ///
    /// Behavior undefined if either of latter two constraints are unmet.
    ///
    /// In addition, `new_kind` should not impose a stronger alignment
    /// constraint than `kind`. (In other words, `new_kind.align()`
    /// must evenly divide `kind.align()`; note this implies the
    /// alignment of `new_kind` must not exceed that of `kind`.)
    /// However, behavior is well-defined (though underspecified) when
    /// this constraint is violated; further discussion below.
    ///
    /// If this returns `Ok`, then ownership of the memory block
    /// referenced by `ptr` has been transferred to this
    /// allocator. The memory may or may not have been freed, and
    /// should be considered unusable (unless of course it was
    /// transferred back to the caller again via the return value of
    /// this method).
    ///
    /// Returns `Err` only if `new_kind` does not meet the allocator's
    /// size and alignment constraints of the allocator or the
    /// alignment of `kind`, or if reallocation otherwise fails. (Note
    /// that did not say "if and only if" -- in particular, an
    /// implementation of this method *can* return `Ok` if
    /// `new_kind.align() > old_kind.align()`; or it can return `Err`
    /// in that scenario.)
    ///
    /// If this method returns `Err`, then ownership of the memory
    /// block has not been transferred to this allocator, and the
    /// contents of the memory block are unaltered.
    unsafe fn realloc(&mut self,
                      ptr: Address,
                      kind: Kind,
                      new_kind: Kind) -> Result<Address, Self::Error> {
        // All Kind alignments are powers of two, so a comparison
        // suffices here (rather than resorting to a `%` operation).
        if new_kind.size() <= self.usable_size(kind) && new_kind.align() <= kind.align() {
            return Ok(ptr);
        } else {
            let result = self.alloc(new_kind);
            if let Ok(new_ptr) = result {
                ptr::copy(*ptr as *const u8, *new_ptr, cmp::min(*kind.size(), *new_kind.size()));
                loop {
                    if let Err(err) = self.dealloc(ptr, kind) {
                        // all we can do from the realloc abstraction
                        // is either:
                        //
                        // 1. free the block we just finished copying
                        //    into and pass the error up,
                        // 2. ignore the dealloc error, or
                        // 3. try again.
                        //
                        // They are all terrible; 1 seems unjustifiable.
                        // So we choose 2, unless the error is transient.
                        if err.is_transient() { continue; }
                    }
                    break;
                }
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
                             new_kind: Kind) -> Result<Excess, Self::Error> {
        self.realloc(ptr, kind, new_kind)
            .map(|p| Excess(p, self.usable_size(new_kind)))
    }

    // == COMMON USAGE PATTERNS ==
    // alloc_one, dealloc_one, alloc_array, realloc_array. dealloc_array
    
    /// Allocates a block suitable for holding an instance of `T`.
    ///
    /// Captures a common usage pattern for allocators.
    ///
    /// The returned block is suitable for passing to the
    /// `alloc`/`realloc` methods of this allocator.
    unsafe fn alloc_one<T>(&mut self) -> Result<Unique<T>, Self::Error> {
        if let Some(k) = Kind::new::<T>() {
            self.alloc(k).map(|p|Unique::new(*p as *mut T))
        } else {
            // (only occurs for zero-sized T)
            debug_assert!(mem::size_of::<T>() == 0);
            Err(Self::Error::invalid_input())
        }
    }

    /// Deallocates a block suitable for holding an instance of `T`.
    ///
    /// Captures a common usage pattern for allocators.
    unsafe fn dealloc_one<T>(&mut self, mut ptr: Unique<T>) -> Result<(), Self::Error> {
        let raw_ptr = NonZero::new(ptr.get_mut() as *mut T as *mut u8);
        self.dealloc(raw_ptr, Kind::new::<T>().unwrap())
    }

    /// Allocates a block suitable for holding `n` instances of `T`.
    ///
    /// Captures a common usage pattern for allocators.
    ///
    /// The returned block is suitable for passing to the
    /// `alloc`/`realloc` methods of this allocator.
    unsafe fn alloc_array<T>(&mut self, n: usize) -> Result<Unique<T>, Self::Error> {
        match Kind::array::<T>(n) {
            Some(kind) => self.alloc(kind).map(|p|Unique::new(*p as *mut T)),
            None => Err(Self::Error::invalid_input()),
        }
    }

    /// Reallocates a block previously suitable for holding `n_old`
    /// instances of `T`, returning a block suitable for holding
    /// `n_new` instances of `T`.
    ///
    /// Captures a common usage pattern for allocators.
    ///
    /// The returned block is suitable for passing to the
    /// `alloc`/`realloc` methods of this allocator.
    unsafe fn realloc_array<T>(&mut self,
                               ptr: Unique<T>,
                               n_old: usize,
                               n_new: usize) -> Result<Unique<T>, Self::Error> {
        let old_new_ptr = (Kind::array::<T>(n_old), Kind::array::<T>(n_new), *ptr);
        if let (Some(k_old), Some(k_new), ptr) = old_new_ptr {
            self.realloc(NonZero::new(ptr as *mut u8), k_old, k_new)
                .map(|p|Unique::new(*p as *mut T))
        } else {
            Err(Self::Error::invalid_input())
        }
    }

    /// Deallocates a block suitable for holding `n` instances of `T`.
    ///
    /// Captures a common usage pattern for allocators.
    unsafe fn dealloc_array<T>(&mut self, ptr: Unique<T>, n: usize) -> Result<(), Self::Error> {
        let raw_ptr = NonZero::new(*ptr as *mut u8);
        if let Some(k) = Kind::array::<T>(n) {
            self.dealloc(raw_ptr, k)
        } else {
            Err(Self::Error::invalid_input())
        }
    }

    // UNCHECKED METHOD VARIANTS

    /// Returns a pointer suitable for holding data described by
    /// `kind`, meeting its size and alignment guarantees.
    ///
    /// The returned block of storage may or may not have its contents
    /// initialized. (Extension subtraits might restrict this
    /// behavior, e.g. to ensure initialization.)
    ///
    /// Returns `None` if request unsatisfied.
    ///
    /// Behavior undefined if input does not meet size or alignment
    /// constraints of this allocator.
    unsafe fn alloc_unchecked(&mut self, kind: Kind) -> Option<Address> {
        // (default implementation carries checks, but impl's are free to omit them.)
        self.alloc(kind).ok()
    }

    /// Deallocate the memory referenced by `ptr`.
    ///
    /// `ptr` must have previously been provided via this allocator,
    /// and `kind` must *fit* the provided block (see above).
    /// Otherwise yields undefined behavior.
    unsafe fn dealloc_unchecked(&mut self, ptr: Address, kind: Kind) {
        // (default implementation carries checks, but impl's are free to omit them.)
        self.dealloc(ptr, kind).unwrap()
    }

    /// Returns a pointer suitable for holding data described by
    /// `new_kind`, meeting its size and alignment guarantees. To
    /// accomplish this, may extend or shrink the allocation
    /// referenced by `ptr` to fit `new_kind`.
    ////
    /// (In other words, ownership of the memory block associated with
    /// `ptr` is first transferred back to this allocator, but the
    /// same block may or may not be transferred back as the result of
    /// this call.)
    ///
    /// * `ptr` must have previously been provided via this allocator.
    ///
    /// * `kind` must *fit* the `ptr` (see above). (The `new_kind`
    ///   argument need not fit it.)
    ///
    /// * `new_kind` must meet the allocator's size and alignment
    ///    constraints. In addition, `new_kind.align()` must equal
    ///    `kind.align()`. (Note that this is a stronger constraint
    ///    that that imposed by `fn realloc`.)
    ///
    /// Behavior undefined if any of latter three constraints are unmet.
    ///
    /// If this returns `Some`, then the memory block referenced by
    /// `ptr` may have been freed and should be considered unusable.
    ///
    /// Returns `None` if reallocation fails; in this scenario, the
    /// original memory block referenced by `ptr` is unaltered.
    unsafe fn realloc_unchecked(&mut self,
                                ptr: Address,
                                kind: Kind,
                                new_kind: Kind) -> Option<Address> {
        // (default implementation carries checks, but impl's are free to omit them.)
        self.realloc(ptr, kind, new_kind).ok()
    }

    /// Behaves like `fn alloc_unchecked`, but also returns the whole
    /// size of the returned block. 
    unsafe fn alloc_excess_unchecked(&mut self, kind: Kind) -> Option<Excess> {
        self.alloc_excess(kind).ok()
    }

    /// Behaves like `fn realloc_unchecked`, but also returns the
    /// whole size of the returned block.
    unsafe fn realloc_excess_unchecked(&mut self,
                                       ptr: Address,
                                       kind: Kind,
                                       new_kind: Kind) -> Option<Excess> {
        self.realloc_excess(ptr, kind, new_kind).ok()
    }


    /// Allocates a block suitable for holding `n` instances of `T`.
    ///
    /// Captures a common usage pattern for allocators.
    ///
    /// Requires inputs are non-zero and do not cause arithmetic
    /// overflow, and `T` is not zero sized; otherwise yields
    /// undefined behavior.
    unsafe fn alloc_array_unchecked<T>(&mut self, n: usize) -> Option<Unique<T>> {
        let kind = Kind::array_unchecked::<T>(n);
        self.alloc_unchecked(kind).map(|p|Unique::new(*p as *mut T))
    }

    /// Reallocates a block suitable for holding `n_old` instances of `T`,
    /// returning a block suitable for holding `n_new` instances of `T`.
    ///
    /// Captures a common usage pattern for allocators.
    ///
    /// Requires inputs are non-zero and do not cause arithmetic
    /// overflow, and `T` is not zero sized; otherwise yields
    /// undefined behavior.
    unsafe fn realloc_array_unchecked<T>(&mut self,
                                         ptr: Unique<T>,
                                         n_old: usize,
                                         n_new: usize) -> Option<Unique<T>> {
        let (k_old, k_new, ptr) = (Kind::array_unchecked::<T>(n_old),
                                   Kind::array_unchecked::<T>(n_new),
                                   *ptr);
        self.realloc_unchecked(NonZero::new(ptr as *mut u8), k_old, k_new)
            .map(|p|Unique::new(*p as *mut T))
    }

    /// Deallocates a block suitable for holding `n` instances of `T`.
    ///
    /// Captures a common usage pattern for allocators.
    ///
    /// Requires inputs are non-zero and do not cause arithmetic
    /// overflow, and `T` is not zero sized; otherwise yields
    /// undefined behavior.
    unsafe fn dealloc_array_unchecked<T>(&mut self, ptr: Unique<T>, n: usize) {
        let kind = Kind::array_unchecked::<T>(n);
        self.dealloc_unchecked(NonZero::new(*ptr as *mut u8), kind);
    }
}
