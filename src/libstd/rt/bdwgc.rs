// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#[allow(dead_code)];
#[allow(non_camel_case_types)];

use libc::{c_ulong, c_char, c_void, c_int, c_uint};
use libc::{pthread_t, pthread_attr_t};
use rt::thread;
use ptr;

pub use collect      = self::GC_gcollect;

pub use pthread_create = self::GC_pthread_create;
pub use pthread_join   = self::GC_pthread_join;
pub use pthread_detach = self::GC_pthread_detach;
pub use pthread_cancel = self::GC_pthread_cancel;
pub use pthread_exit   = self::GC_pthread_exit;

// pub use malloc_atomic                = self::GC_malloc_atomic;
pub use exchange_malloc_atomic = self::GC_debug_exchange_malloc_replacement;
pub use proc_malloc_atomic     = self::GC_debug_proc_malloc_replacement;
pub use managed_malloc_atomic  = self::GC_debug_managed_malloc_replacement;
pub use other_malloc_atomic    = self::GC_debug_other_malloc_replacement;

// pub use malloc_atomic_uncollectable  = self::GC_malloc_atomic_uncollectable;
pub use exchange_malloc_atomic_uncollectable = self::debug_exchange_malloc_uncollectable;
pub use proc_malloc_atomic_uncollectable     = self::debug_proc_malloc_uncollectable;
pub use other_malloc_atomic_uncollectable    = self::debug_other_malloc_uncollectable;

// pub use malloc_uncollectable         = self::GC_malloc_uncollectable;
pub use exchange_malloc_uncollectable      = self::debug_exchange_malloc_uncollectable;
pub use proc_malloc_uncollectable          = self::debug_proc_malloc_uncollectable;
pub use other_malloc_uncollectable         = self::debug_other_malloc_uncollectable;

// pub use realloc                      = self::GC_realloc;
pub use exchange_realloc                = self::debug_exchange_realloc;
pub use proc_realloc                    = self::debug_proc_realloc;
pub use managed_realloc                 = self::debug_managed_realloc;
pub use other_realloc                   = self::debug_other_realloc;

pub unsafe fn collect_from(where: uint) {
    GC_gcollect_from(where as c_uint)
}

// pub use free                        = self::GC_free;
// pub use malloc                      = self::GC_malloc;

pub fn init() {
    unsafe {

        // A free-space-divisor of K means bdw tries to allocate N/K
        // bytes between collections, where (approximately)
        //   N = 2*|traced| + |untraced| + |root set|
        // in bytes.  The relationship between the N above and the
        // heap size H is non-obvious, but we can get some rough bounds
        // by noting that H < N < 2*H.
        // Thus the inverse load factor L = (H + N/K) / H
        //              (H + H/K) / H < L < (H + 2*H/K) / H
        //                  (1 + 1/K) < L < (1 + 2/K)
        //
        // So:
        //    K = 1 implies    2 < L < 3
        //    K = 2 implies  1.5 < L < 2
        //    K = 4 implies 1.25 < L < 1.5
        //   K = 20 implies 1.05 < L < 1.1
        //   K = 50 implies 1.02 < L < 1.04
        //  k = 100 implies 1.01 < L < 1.02
        //
        // Temporarily, I am putting in an absurdly small inverse load
        // factor to try to catch GC-related bugs as quickly as
        // possible during this initial development process.
        // GC_set_free_space_divisor(100);

        GC_init();
    }
}

// wrappers to deal with BDW not offering full set of drop-in _replacement variants.
#[cfg(bdw_pristine_api)]
unsafe fn debug_malloc_uncollectable(size_in_bytes: size_t) -> *c_void {
    GC_debug_malloc_uncollectable(size_in_bytes, ptr::null(), 0) as *c_void
}
unsafe fn debug_exchange_malloc_uncollectable(size_in_bytes: size_t) -> *c_void {
    GC_debug_exchange_malloc_uncollectable(size_in_bytes, ptr::null(), 0) as *c_void
}
unsafe fn debug_proc_malloc_uncollectable(size_in_bytes: size_t) -> *c_void {
    GC_debug_proc_malloc_uncollectable(size_in_bytes, ptr::null(), 0) as *c_void
}
unsafe fn debug_other_malloc_uncollectable(size_in_bytes: size_t) -> *c_void {
    GC_debug_other_malloc_uncollectable(size_in_bytes, ptr::null(), 0) as *c_void
}

// wrappers to deal with BDW not offering full set of drop-in _replacement variants.
#[cfg(bdw_pristine_api)]
unsafe fn debug_realloc(old: *mut c_void, size_in_bytes: size_t) -> *mut c_void {
    GC_debug_realloc(old, size_in_bytes, ptr::null(), 0)
}
unsafe fn debug_exchange_realloc(old: *mut c_void, size_in_bytes: size_t) -> *mut c_void {
    GC_debug_exchange_realloc(old, size_in_bytes, ptr::null(), 0)
}
unsafe fn debug_proc_realloc(old: *mut c_void, size_in_bytes: size_t) -> *mut c_void {
    GC_debug_proc_realloc(old, size_in_bytes, ptr::null(), 0)
}
unsafe fn debug_managed_realloc(old: *mut c_void, size_in_bytes: size_t) -> *mut c_void {
    GC_debug_managed_realloc(old, size_in_bytes, ptr::null(), 0)
}
unsafe fn debug_other_realloc(old: *mut c_void, size_in_bytes: size_t) -> *mut c_void {
    GC_debug_other_realloc(old, size_in_bytes, ptr::null(), 0)
}

// wrappers compatible with current libc::malloc's lack of mutability.
#[cfg(bdw_pristine_api)]
pub unsafe fn malloc(size_in_bytes: size_t) -> *c_void {
    GC_debug_malloc_replacement(size_in_bytes) as *c_void
}
pub unsafe fn exchange_malloc(size_in_bytes: size_t) -> *c_void {
    GC_debug_exchange_malloc_replacement(size_in_bytes) as *c_void
}
pub unsafe fn proc_malloc(size_in_bytes: size_t) -> *c_void {
    GC_debug_proc_malloc_replacement(size_in_bytes) as *c_void
}
pub unsafe fn managed_malloc(size_in_bytes: size_t) -> *c_void {
    GC_debug_managed_malloc_replacement(size_in_bytes) as *c_void
}
pub unsafe fn other_malloc(size_in_bytes: size_t) -> *c_void {
    GC_debug_other_malloc_replacement(size_in_bytes) as *c_void
}

#[cfg(bdw_pristine_api)]
pub unsafe fn free(arg1: *c_void) {
    GC_debug_free(arg1 as *mut c_void)
}
pub unsafe fn exchange_free(arg1: *c_void) {
    GC_debug_exchange_free(arg1 as *mut c_void)
}
pub unsafe fn proc_free(arg1: *c_void) {
    GC_debug_proc_free(arg1 as *mut c_void)
}
pub unsafe fn managed_free(arg1: *c_void) {
    GC_debug_managed_free(arg1 as *mut c_void)
}
pub unsafe fn other_free(arg1: *c_void) {
    GC_debug_other_free(arg1 as *mut c_void)
}


type size_t = c_ulong;

type sigset_t = c_void; // (temporary hack to get things building)

/// Define word and signed_word to be unsigned and signed types of the
/// size as char * or void *.  There seems to be no way to do this
/// even semi-portably.  The following is probably no better/worse
/// than almost anything else.
/// The ANSI standard suggests that size_t and ptrdiff_t might be
/// better choices.  But those had incorrect definitions on some older
/// systems.  Notably "typedef int size_t" is WRONG.
type GC_word = c_ulong;

type GC_oom_func  = extern "C" fn(bytes_requested: size_t) -> *mut c_void;
type GC_finalizer_notifier_proc = extern "C" fn();
type GC_stop_func = extern "C" fn() -> c_int;

/// Finalization.  Some of these primitives are grossly unsafe.
/// The idea is to make them both cheap, and sufficient to build
/// a safer layer, closer to Modula-3, Java, or PCedar finalization.
/// The interface represents my conclusions from a long discussion
/// with Alan Demers, Dan Greene, Carl Hauser, Barry Hayes,
/// Christian Jacobi, and Russ Atkinson.  It's not perfect, and
/// probably nobody else agrees with it.     Hans-J. Boehm  3/13/92
type GC_finalization_proc = extern "C" fn(obj: *mut c_void, client_data: *mut c_void);

type GC_warn_proc = extern "C" fn(msg: *mut c_char, arg: GC_word);
type GC_hidden_pointer = GC_word;
type GC_fn_type = extern "C" fn(client_data: *mut c_void) -> *mut c_void;
type GC_on_heap_resize_proc = extern "C" fn(new_size: GC_word);

struct Struct_GC_stack_base {
    mem_base: *mut c_void,
    // (N.B.: on Itanium, there is a separate register stack void* field here.)
}
type GC_stack_base_func = extern "C" fn(sb: *mut Struct_GC_stack_base,
                                            arg: *mut c_void) -> *mut c_void;

/// A filter function to control the scanning of dynamic libraries.
/// If implemented, called by GC before registering a dynamic library
/// (discovered by GC) section as a static data root (called only as
/// a last reason not to register).  The filename of the library, the
/// address and the length of the memory region (section) are passed.
/// This routine should return nonzero if that region should be scanned.
/// Always called with the allocation lock held.  Depending on the
/// platform, might be called with the "world" stopped.
type GC_has_static_roots_func = extern "C" fn(dlpi_name: *c_char,
                                                  section_start: *mut c_void,
                                                  section_size: size_t) -> c_int;

type GC_abort_func = extern "C" fn(msg: *c_char);

struct GC_prof_stats_s {
    /// Heap size in bytes (including the area unmapped to OS).
    /// Same as GC_get_heap_size() + GC_get_unmapped_bytes().
    heapsize_full: GC_word,
    /// Total bytes contained in free and unmapped blocks.
    /// Same as GC_get_free_bytes() + GC_get_unmapped_bytes().
    free_bytes_full: GC_word,
    /// Amount of memory unmapped to OS.  Same as the value
    /// returned by GC_get_unmapped_bytes().
    unmapped_bytes: GC_word,
    /// Number of bytes allocated since the recent collection.
    /// Same as returned by GC_get_bytes_since_gc().
    bytes_allocd_since_gc: GC_word,
    /// Number of bytes allocated before the recent garbage
    /// collection.  The value may wrap.  Same as the result of
    /// GC_get_total_bytes() - GC_get_bytes_since_gc().
    allocd_bytes_before_gc: GC_word,
    /// Number of bytes not considered candidates for garbage
    /// collection.  Same as returned by GC_get_non_gc_bytes().
    non_gc_bytes: GC_word,
    /// Garbage collection cycle number.  The value may wrap
    /// (and could be -1).  Same as returned by GC_get_gc_no().
    gc_no: GC_word,
    /// Number of marker threads (excluding the initiating one).
    /// Same as returned by GC_get_parallel (or 0 if the
    /// collector is single-threaded).
    markers_m1: GC_word,
    /// Approximate number of reclaimed bytes after recent GC.
    bytes_reclaimed_since_gc: GC_word,
    /// Approximate number of bytes reclaimed before the recent
    /// garbage collection.  The value may wrap.
    reclaimed_bytes_before_gc: GC_word,
}

/// Setting GC_time_limit to this value
/// will disable the "pause time exceeded"
/// tests.
pub static GC_TIME_UNLIMITED : c_ulong = 999999;

// Link to BDW libgc
#[link(name = "gc", kind = "static")]
extern "C" {
    /// Get the GC library version. The returned value is a constant in the
    /// form: ((version_major<<16) | (version_minor<<8) | version_micro).
    fn GC_get_version() -> c_uint;

    /// Public read-only "variables" (i.e. getters).

    /// Counter incremented per collection.
    /// Includes empty GCs at startup.
    ///
    /// GC_get_gc_no() is unsynchronized, so
    /// it requires GC_call_with_alloc_lock() to
    /// avoid data races on multiprocessors.
    fn GC_get_gc_no() -> GC_word;

    /// Public R/W "variables" (i.e. getters/setters).

    /// When there is insufficient memory to satisfy
    /// an allocation request, we return
    /// (*GC_oom_fn)(size).  By default this just
    /// returns NULL.
    /// If it returns, it must return 0 or a valid
    /// pointer to a previously allocated heap
    /// object.  GC_oom_fn must not be 0.
    /// Both the supplied setter and the getter
    /// acquire the GC lock (to avoid data races).
    fn GC_set_oom_fn(f: GC_oom_func);
    fn GC_get_oom_fn() -> GC_oom_func;

    /// Invoked when the heap grows or shrinks.
    /// Called with the world stopped (and the
    /// allocation lock held).  May be 0.
    ///
    /// Both the supplied setter and the getter
    /// acquire the GC lock (to avoid data races).
    fn GC_set_on_heap_resize(p: GC_on_heap_resize_proc);

    /// Both the supplied setter and the getter
    /// acquire the GC lock (to avoid data races).
    fn GC_get_on_heap_resize() -> GC_on_heap_resize_proc;

    /// Do not actually garbage collect, but simply
    /// report inaccessible memory that was not
    /// deallocated with GC_free.  Initial value
    /// is determined by FIND_LEAK macro.
    /// The value should not typically be modified
    /// after GC initialization (and, thus, it does
    /// not use or need synchronization).
    fn GC_set_find_leak(flag: c_int);
    fn GC_get_find_leak() -> c_int;

    /// Arrange for pointers to object interiors to
    /// be recognized as valid.  Typically should
    /// not be changed after GC initialization (in
    /// case of calling it after the GC is
    /// initialized, the setter acquires the GC lock
    /// (to avoid data races).  The initial value
    /// depends on whether the GC is built with
    /// ALL_INTERIOR_POINTERS macro defined or not.
    /// Unless DONT_ADD_BYTE_AT_END is defined, this
    /// also affects whether sizes are increased by
    /// at least a byte to allow "off the end"
    /// pointer recognition.  Must be only 0 or 1.
    fn GC_set_all_interior_pointers(flag: c_int);
    fn GC_get_all_interior_pointers() -> c_int;

    /// If nonzero, finalizers will only be run in
    /// response to an explicit GC_invoke_finalizers
    /// call.  The default is determined by whether
    /// the FINALIZE_ON_DEMAND macro is defined
    /// when the collector is built.
    /// The setter and getter are unsynchronized.
    fn GC_set_finalize_on_demand(flag: c_int);
    fn GC_get_finalize_on_demand() -> c_int;

    /// Mark objects reachable from finalizable
    /// objects in a separate post-pass.  This makes
    /// it a bit safer to use non-topologically-
    /// ordered finalization.  Default value is
    /// determined by JAVA_FINALIZATION macro.
    /// Enables register_finalizer_unreachable to
    /// work correctly.
    /// The setter and getter are unsynchronized.
    fn GC_set_java_finalization(flag: c_int);
    fn GC_get_java_finalization() -> c_int;

    /// Invoked by the collector when there are
    /// objects to be finalized.  Invoked at most
    /// once per GC cycle.  Never invoked unless
    /// GC_finalize_on_demand is set.
    /// Typically this will notify a finalization
    /// thread, which will call GC_invoke_finalizers
    /// in response.  May be 0 (means no notifier).
    /// Both the supplied setter and the getter
    /// acquire the GC lock (to avoid data races).
    fn GC_set_finalizer_notifier(flag: GC_finalizer_notifier_proc);
    fn GC_get_finalizer_notifier() -> GC_finalizer_notifier_proc;

    /// Do not expand the heap unless explicitly
    /// requested or forced to.  The setter and
    /// getter are unsynchronized.
    fn GC_set_dont_expand(arg1: c_int);
    fn GC_get_dont_expand() -> c_int;

    #[cfg(bdw_support_incremental)]
    fn GC_set_full_freq(arg1: c_int);
    #[cfg(bdw_support_incremental)]
    fn GC_get_full_freq() -> c_int;

    /// Bytes not considered candidates for
    /// collection.  Used only to control scheduling
    /// of collections.  Updated by
    /// GC_malloc_uncollectable and GC_free.
    /// Wizards only.
    /// The setter and getter are unsynchronized, so
    /// GC_call_with_alloc_lock() is required to
    /// avoid data races (if the value is modified
    /// after the GC is put to multi-threaded mode).
    fn GC_set_non_gc_bytes(arg1: GC_word);
    fn GC_get_non_gc_bytes() -> GC_word;

    /// Don't register dynamic library data segments.
    /// Wizards only.  Should be used only if the
    /// application explicitly registers all roots.
    /// (In some environments like Microsoft Windows
    /// and Apple's Darwin, this may also prevent
    /// registration of the main data segment as part
    /// of the root set.)
    /// The setter and getter are unsynchronized.
    fn GC_set_no_dls(arg1: c_int);
    fn GC_get_no_dls() -> c_int;

    /// We try to make sure that we allocate at
    /// least N/GC_free_space_divisor bytes between
    /// collections, where N is twice the number
    /// of traced bytes, plus the number of untraced
    /// bytes (bytes in "atomic" objects), plus
    /// a rough estimate of the root set size.
    /// N approximates GC tracing work per GC.
    /// Initially, GC_free_space_divisor = 3.
    /// Increasing its value will use less space
    /// but more collection time.  Decreasing it
    /// will appreciably decrease collection time
    /// at the expense of space.
    /// The setter and getter are unsynchronized, so
    /// GC_call_with_alloc_lock() is required to
    /// avoid data races (if the value is modified
    /// after the GC is put to multi-threaded mode).
    fn GC_set_free_space_divisor(arg1: GC_word);
    fn GC_get_free_space_divisor() -> GC_word;

    /// The maximum number of GCs attempted before
    /// reporting out of memory after heap
    /// expansion fails.  Initially 0.
    /// The setter and getter are unsynchronized, so
    /// GC_call_with_alloc_lock() is required to
    /// avoid data races (if the value is modified
    /// after the GC is put to multi-threaded mode).
    fn GC_set_max_retries(arg1: GC_word);
    fn GC_get_max_retries() -> GC_word;

    /// Do not collect as part of GC
    /// initialization.  Should be set only
    /// if the client wants a chance to
    /// manually initialize the root set
    /// before the first collection.
    /// Interferes with blacklisting.
    /// Wizards only.  The setter and getter
    /// are unsynchronized (and no external
    /// locking is needed since the value is
    /// accessed at GC initialization only).
    fn GC_set_dont_precollect(arg1: c_int);
    fn GC_get_dont_precollect() -> c_int;

    /// If incremental collection is enabled,
    /// We try to terminate collections
    /// after this many milliseconds.  Not a
    /// hard time bound.  Setting this to
    /// GC_TIME_UNLIMITED will essentially
    /// disable incremental collection while
    /// leaving generational collection
    /// enabled.
    ///
    /// The setter and getter are unsynchronized, so
    /// GC_call_with_alloc_lock() is required to
    /// avoid data races (if the value is modified
    /// after the GC is put to multi-threaded mode).
    #[cfg(bdw_support_incremental)]
    fn GC_set_time_limit(limit: c_ulong);
    #[cfg(bdw_support_incremental)]
    fn GC_get_time_limit() -> c_ulong;

    /// Set whether the GC will allocate executable memory pages or not.
    /// A non-zero argument instructs the collector to allocate memory with
    /// the executable flag on.  Must be called before the collector is
    /// initialized.  May have no effect on some platforms.  The default
    /// value is controlled by NO_EXECUTE_PERMISSION macro (if present then
    /// the flag is off).  Portable clients should have
    /// GC_set_pages_executable(1) call (before GC_INIT) provided they are
    /// going to execute code on any of the GC-allocated memory objects.
    fn GC_set_pages_executable(arg1: c_int);

    /// Returns non-zero value if the GC is set to the allocate-executable
    /// mode.  The mode could be changed by GC_set_pages_executable (before
    /// GC_INIT) unless the former has no effect on the platform.  Does not
    /// use or need synchronization (i.e. acquiring the allocator lock).
    fn GC_get_pages_executable() -> c_int;

    /// Overrides the default handle-fork mode.  Non-zero value means GC
    /// should install proper pthread_atfork handlers.  Has effect only if
    /// called before GC_INIT.  Clients should invoke GC_set_handle_fork
    /// with non-zero argument if going to use fork with GC functions called
    /// in the forked child.  (Note that such client and atfork handlers
    /// activities are not fully POSIX-compliant.)  GC_set_handle_fork
    /// instructs GC_init to setup GC fork handlers using pthread_atfork,
    /// the latter might fail (or, even, absent on some targets) causing
    /// abort at GC initialization.  Starting from 7.3alpha3, problems with
    /// missing (or failed) pthread_atfork() could be avoided by invocation
    /// of GC_set_handle_fork(-1) at application start-up and surrounding
    /// each fork() with the relevant GC_atfork_prepare/parent/child calls.
    fn GC_set_handle_fork(arg1: c_int);

    /// Routines to handle POSIX fork() manually (no-op if handled
    /// automatically).
    ///
    /// GC_atfork_prepare should be called immediately before fork().
    fn GC_atfork_prepare();
    /// Routines to handle POSIX fork() manually (no-op if handled
    /// automatically).
    ///
    /// GC_atfork_parent should be invoked just after fork in the
    /// branch that corresponds to parent process (i.e., fork result
    /// is non-zero).
    fn GC_atfork_parent();
    /// Routines to handle POSIX fork() manually (no-op if handled
    /// automatically).
    ///
    /// GC_atfork_child is to be called immediately in the child
    /// branch (i.e., fork result is 0). Note that GC_atfork_child()
    /// call should, of course, precede GC_start_mark_threads call (if
    /// any).
    fn GC_atfork_child();

    /// Initialize the collector.  Portable clients should call GC_INIT()
    /// from the main program instead.
    ///
    /// Fully portable code should call GC_INIT() from the main program
    /// before making any other GC_ calls.  On most platforms this is a
    /// no-op and the collector self-initializes.  But a number of
    /// platforms make that too hard.
    ///
    /// A GC_INIT call is required if the collector is built with
    /// THREAD_LOCAL_ALLOC defined and the initial allocation call is not
    /// to GC_malloc() or GC_malloc_atomic().
    ///
    fn GC_init();
    // N.B.: The GC_INIT definiition circa v7.5.0 is:
    //
    //   GC_INIT_CONF_{DONT_EXPAND, FORCE_UNMAP_ON_GCOLLECT, MAX_RETRIES,
    //                 FREE_SPACE_DIVISOR, FULL_FREQ, TIME_LIMIT,
    //                 SUSPEND_SIGNAL, THR_RESTART_SIGNAL, MAXIMUM_HEAP_SIZE};
    //   GC_init();
    //   GC_INIT_CONF_{ROOTS, IGNORE_WARN, INITIAL_HEAP_SIZE};
    //
    // each of which initializes the corresponding piece of state based on
    // compile-time preprocessor settings.

    /// General purpose allocation routines, with roughly malloc calling
    /// conv.  The atomic versions promise that no relevant pointers are
    /// contained in the object.  The non-atomic versions guarantee that the
    /// new object is cleared.  GC_malloc_stubborn promises that no changes
    /// to the object will occur after GC_end_stubborn_change has been
    /// called on the result of GC_malloc_stubborn.  GC_malloc_uncollectable
    /// allocates an object that is scanned for pointers to collectible
    /// objects, but is not itself collectible.  The object is scanned even
    /// if it does not appear to be reachable.  GC_malloc_uncollectable and
    /// GC_free called on the resulting object implicitly update
    /// GC_non_gc_bytes appropriately.

    /// Replace calls to malloc by calls to GC_malloc (or GC_debug_malloc_replacement).
    ///
    /// Non-atomic versions guarantee that the new object is cleared.
    #[cfg(bdw_pristine_api)]
    fn GC_malloc(size_in_bytes: size_t) -> *mut c_void;
    fn GC_exchange_malloc(size_in_bytes: size_t) -> *mut c_void;
    fn GC_proc_malloc(size_in_bytes: size_t) -> *mut c_void;
    fn GC_managed_malloc(size_in_bytes: size_t) -> *mut c_void;
    fn GC_other_malloc(size_in_bytes: size_t) -> *mut c_void;

    #[cfg(bdw_pristine_api)]
    fn GC_debug_malloc(size_in_bytes: size_t,
                           file: *c_char, lineno: c_int) -> *mut c_void;
    fn GC_debug_exchange_malloc(size_in_bytes: size_t,
                           file: *c_char, lineno: c_int) -> *mut c_void;
    fn GC_debug_proc_malloc(size_in_bytes: size_t,
                           file: *c_char, lineno: c_int) -> *mut c_void;
    fn GC_debug_managed_malloc(size_in_bytes: size_t,
                           file: *c_char, lineno: c_int) -> *mut c_void;
    fn GC_debug_other_malloc(size_in_bytes: size_t,
                           file: *c_char, lineno: c_int) -> *mut c_void;

    /// Routines that allocate objects with debug information (like the
    /// above), but just fill in dummy file and line number information.
    /// Thus they can serve as drop-in malloc/realloc replacements.  This
    /// can be useful for two reasons:
    /// 1) It allows the collector to be built with DBG_HDRS_ALL defined
    ///    even if some allocation calls come from 3rd party libraries
    ///    that can't be recompiled.
    /// 2) On some platforms, the file and line information is redundant,
    ///    since it can be reconstructed from a stack trace.  On such
    ///    platforms it may be more convenient not to recompile, e.g. for
    ///    leak detection.  This can be accomplished by instructing the
    ///    linker to replace malloc/realloc with these.
    #[cfg(bdw_pristine_api)]
    fn GC_debug_malloc_replacement(size_in_bytes: size_t) -> *mut c_void;
    fn GC_debug_exchange_malloc_replacement(size_in_bytes: size_t) -> *mut c_void;
    fn GC_debug_proc_malloc_replacement(size_in_bytes: size_t) -> *mut c_void;
    fn GC_debug_managed_malloc_replacement(size_in_bytes: size_t) -> *mut c_void;
    fn GC_debug_other_malloc_replacement(size_in_bytes: size_t) -> *mut c_void;

    fn GC_strdup(s: *c_char) -> *mut c_char;
    fn GC_debug_strdup(s: *c_char, file: *c_char, lineno: c_int) -> *mut c_char;
    fn GC_strndup(s: *c_char, n: size_t) -> *mut c_char;
    fn GC_debug_strndup(s: *c_char, n: size_t, file: *c_char, lineno: c_int) -> *mut c_char;

    /// For compatibility with C library.  This is occasionally faster than
    /// a malloc followed by a bcopy.  But if you rely on that, either here
    /// or with the standard C library, your code is broken.  In my
    /// opinion, it shouldn't have been invented, but now we're stuck. -HB
    /// The resulting object has the same kind as the original.
    /// If the argument is stubborn, the result will have changes enabled.
    /// It is an error to have changes enabled for the original object.
    /// Follows ANSI conventions for NULL old_object.
    ///
    /// Replace calls to realloc by calls to GC_realloc (or GC_debug_realloc_replacement).
    #[cfg(bdw_pristine_api)]
    fn GC_realloc(old: *mut c_void, size_in_bytes: size_t) -> *mut c_void;
    fn GC_exchange_realloc(old: *mut c_void, size_in_bytes: size_t) -> *mut c_void;
    fn GC_proc_realloc(old: *mut c_void, size_in_bytes: size_t) -> *mut c_void;
    fn GC_managed_realloc(old: *mut c_void, size_in_bytes: size_t) -> *mut c_void;
    fn GC_other_realloc(old: *mut c_void, size_in_bytes: size_t) -> *mut c_void;

    #[cfg(bdw_pristine_api)]
    fn GC_debug_realloc(old: *mut c_void, size_in_bytes: size_t,
                            file: *c_char, lineno: c_int) -> *mut c_void;
    fn GC_debug_exchange_realloc(old: *mut c_void, size_in_bytes: size_t,
                            file: *c_char, lineno: c_int) -> *mut c_void;
    fn GC_debug_proc_realloc(old: *mut c_void, size_in_bytes: size_t,
                            file: *c_char, lineno: c_int) -> *mut c_void;
    fn GC_debug_managed_realloc(old: *mut c_void, size_in_bytes: size_t,
                            file: *c_char, lineno: c_int) -> *mut c_void;
    fn GC_debug_other_realloc(old: *mut c_void, size_in_bytes: size_t,
                            file: *c_char, lineno: c_int) -> *mut c_void;

    /// Routines that allocate objects with debug information (like the
    /// above), but just fill in dummy file and line number information.
    /// Thus they can serve as drop-in malloc/realloc replacements.  This
    /// can be useful for two reasons:
    /// 1) It allows the collector to be built with DBG_HDRS_ALL defined
    ///    even if some allocation calls come from 3rd party libraries
    ///    that can't be recompiled.
    /// 2) On some platforms, the file and line information is redundant,
    ///    since it can be reconstructed from a stack trace.  On such
    ///    platforms it may be more convenient not to recompile, e.g. for
    ///    leak detection.  This can be accomplished by instructing the
    ///    linker to replace malloc/realloc with these.
    #[cfg(bdw_pristine_api)]
    fn GC_debug_realloc_replacement(old: *mut c_void, size_in_bytes: size_t) -> *mut c_void;
    fn GC_debug_exchange_realloc_replacement(old: *mut c_void, size_in_bytes: size_t) -> *mut c_void;
    fn GC_debug_proc_realloc_replacement(old: *mut c_void, size_in_bytes: size_t) -> *mut c_void;
    fn GC_debug_managed_realloc_replacement(old: *mut c_void, size_in_bytes: size_t) -> *mut c_void;
    fn GC_debug_other_realloc_replacement(old: *mut c_void, size_in_bytes: size_t) -> *mut c_void;

    /// If the object is known to never contain pointers, use
    /// GC_malloc_atomic instead of GC_malloc.
    ///
    /// The atomic versions promise that no relevant pointers are
    /// contained in the object.
    #[cfg(bdw_pristine_api)]
    fn GC_malloc_atomic(size_in_bytes: size_t) -> *mut c_void;
    fn GC_exchange_malloc_atomic(size_in_bytes: size_t) -> *mut c_void;
    fn GC_proc_malloc_atomic(size_in_bytes: size_t) -> *mut c_void;
    fn GC_managed_malloc_atomic(size_in_bytes: size_t) -> *mut c_void;
    fn GC_other_malloc_atomic(size_in_bytes: size_t) -> *mut c_void;

    #[cfg(bdw_pristine_api)]
    fn GC_debug_malloc_atomic(size_in_bytes: size_t,
                                  file: *c_char, lineno: c_int) -> *mut c_void;
    fn GC_debug_exchange_malloc_atomic(size_in_bytes: size_t,
                                  file: *c_char, lineno: c_int) -> *mut c_void;
    fn GC_debug_proc_malloc_atomic(size_in_bytes: size_t,
                                  file: *c_char, lineno: c_int) -> *mut c_void;
    fn GC_debug_managed_malloc_atomic(size_in_bytes: size_t,
                                  file: *c_char, lineno: c_int) -> *mut c_void;
    fn GC_debug_other_malloc_atomic(size_in_bytes: size_t,
                                  file: *c_char, lineno: c_int) -> *mut c_void;

    /// GC_malloc_uncollectable allocates an object that is scanned
    /// for pointers to collectible objects, but is not itself
    /// collectible.  The object is scanned even if it does not appear
    /// to be reachable.
    ///
    /// GC_malloc_uncollectable and GC_free called on the resulting
    /// object implicitly update GC_non_gc_bytes appropriately.
    #[cfg(bdw_pristine_api)]
    fn GC_malloc_uncollectable(size_in_bytes: size_t) -> *mut c_void;
    fn GC_exchange_malloc_uncollectable(size_in_bytes: size_t) -> *mut c_void;
    fn GC_proc_malloc_uncollectable(size_in_bytes: size_t) -> *mut c_void;
    fn GC_other_malloc_uncollectable(size_in_bytes: size_t) -> *mut c_void;

    #[cfg(bdw_pristine_api)]
    fn GC_debug_malloc_uncollectable(size_in_bytes: size_t,
                                         file: *c_char, lineno: c_int) -> *mut c_void;
    fn GC_debug_exchange_malloc_uncollectable(size_in_bytes: size_t,
                                         file: *c_char, lineno: c_int) -> *mut c_void;
    fn GC_debug_proc_malloc_uncollectable(size_in_bytes: size_t,
                                         file: *c_char, lineno: c_int) -> *mut c_void;
    fn GC_debug_other_malloc_uncollectable(size_in_bytes: size_t,
                                         file: *c_char, lineno: c_int) -> *mut c_void;

    /// GC_memalign() is not well tested.
    #[cfg(bdw_risky)]
    fn GC_memalign(align: size_t, lb: size_t) -> *mut c_void;
    #[cfg(bdw_risky)]
    fn GC_posix_memalign(memptr: *mut *mut c_void, align: size_t,
                             lb: size_t) -> c_int;

    /// Explicitly deallocate an object.  Dangerous if used incorrectly.
    /// Requires a pointer to the base of an object.
    /// If the argument is stubborn, it should not be changeable when freed.
    /// An object should not be enabled for finalization when it is
    /// explicitly deallocated.
    /// GC_free(0) is a no-op, as required by ANSI C for free.
    #[cfg(bdw_pristine_api)]
    fn GC_free(arg1: *mut c_void);

    fn GC_exchange_free(arg1: *mut c_void);
    fn GC_proc_free(arg1: *mut c_void);
    fn GC_managed_free(arg1: *mut c_void);
    fn GC_other_free(arg1: *mut c_void);

    #[cfg(bdw_pristine_api)]
    fn GC_debug_free(arg1: *mut c_void);
    fn GC_debug_exchange_free(arg1: *mut c_void);
    fn GC_debug_proc_free(arg1: *mut c_void);
    fn GC_debug_managed_free(arg1: *mut c_void);
    fn GC_debug_other_free(arg1: *mut c_void);

    /// Return a pointer to the base (lowest address) of an object given
    /// a pointer to a location within the object.
    /// I.e., map an interior pointer to the corresponding base pointer.
    /// Note that with debugging allocation, this returns a pointer to the
    /// actual base of the object, i.e. the debug information, not to
    /// the base of the user object.
    /// Return 0 if displaced_pointer doesn't point to within a valid
    /// object.
    /// Note that a deallocated object in the garbage collected heap
    /// may be considered valid, even if it has been deallocated with
    /// GC_free.
    fn GC_base(arg1: *mut c_void) -> *mut c_void;

    /// Return non-zero (TRUE) if and only if the argument points to
    /// somewhere in GC heap.  Primary use is as a fast alternative to
    /// GC_base to check whether the pointed object is allocated by GC
    /// or not.  It is assumed that the collector is already initialized.
    fn GC_is_heap_ptr(interior_ptr: *c_void) -> c_int;

    /// Given a pointer to the base of an object, return its size in bytes.
    /// The returned size may be slightly larger than what was originally
    /// requested.
    fn GC_size(obj_addr: *c_void) -> size_t;

    /// Explicitly increase the heap size.
    /// Returns 0 on failure, 1 on success.
    fn GC_expand_hp(number_of_bytes: size_t) -> c_int;

    /// Limit the heap size to n bytes.  Useful when you're debugging,
    /// especially on systems that don't handle running out of memory well.
    /// n == 0 ==> unbounded.  This is the default.  This setter function is
    /// unsynchronized (so it might require GC_call_with_alloc_lock to avoid
    /// data races).
    fn GC_set_max_heap_size(n: GC_word);

    /// Inform the collector that a certain section of statically allocated
    /// memory contains no pointers to garbage collected memory.  Thus it
    /// need not be scanned.  This is sometimes important if the application
    /// maps large read/write files into the address space, which could be
    /// mistaken for dynamic library data segments on some systems.
    /// Both section start and end are not needed to be pointer-aligned.
    fn GC_exclude_static_roots(low_address: *mut c_void, high_address_plus_1: *mut c_void);

    /// Clear the set of root segments.  Wizards only.
    fn GC_clear_roots();

    /// Add a root segment.  Wizards only.
    /// Both segment start and end are not needed to be pointer-aligned.
    /// low_address must not be greater than high_address_plus_1.
    fn GC_add_roots(low_address: *mut c_void, high_address_plus_1: *mut c_void);

    /// Remove a root segment.  Wizards only.
    /// May be unimplemented on some platforms.
    fn GC_remove_roots(low_address: *mut c_void, high_address_plus_1: *mut c_void);

    /// Add a displacement to the set of those considered valid by the
    /// collector.  GC_register_displacement(n) means that if p was returned
    /// by GC_malloc, then (char *)p + n will be considered to be a valid
    /// pointer to p.  N must be small and less than the size of p.
    /// (All pointers to the interior of objects from the stack are
    /// considered valid in any case.  This applies to heap objects and
    /// static data.)
    /// Preferably, this should be called before any other GC procedures.
    /// Calling it later adds to the probability of excess memory
    /// retention.
    /// This is a no-op if the collector has recognition of
    /// arbitrary interior pointers enabled, which is now the default.
    fn GC_register_displacement(arg1: size_t);

    /// The following version should be used if any debugging allocation is
    /// being done.
    fn GC_debug_register_displacement(arg1: size_t);

    /// Explicitly trigger a full, world-stop collection.
    fn GC_gcollect();
    fn GC_gcollect_from(context: c_uint);

    /// Same as above but ignores the default stop_func setting and tries to
    /// unmap as much memory as possible (regardless of the corresponding
    /// switch setting).  The recommended usage: on receiving a system
    /// low-memory event; before retrying a system call failed because of
    /// the system is running out of resources.
    fn GC_gcollect_and_unmap();

    /// Trigger a full world-stopped collection.  Abort the collection if
    /// and when stop_func returns a nonzero value.  Stop_func will be
    /// called frequently, and should be reasonably fast.  (stop_func is
    /// called with the allocation lock held and the world might be stopped;
    /// it's not allowed for stop_func to manipulate pointers to the garbage
    /// collected heap or call most of GC functions.)  This works even
    /// if virtual dirty bits, and hence incremental collection is not
    /// available for this architecture.  Collections can be aborted faster
    /// than normal pause times for incremental collection.  However,
    /// aborted collections do no useful work; the next collection needs
    /// to start from the beginning.  stop_func must not be 0.
    /// GC_try_to_collect() returns 0 if the collection was aborted (or the
    /// collections are disabled), 1 if it succeeded.
    fn GC_try_to_collect(stop_func: GC_stop_func) -> c_int;

    /// Set and get the default stop_func.  The default stop_func is used by
    /// GC_gcollect() and by implicitly trigged collections (except for the
    /// case when handling out of memory).  Must not be 0.
    /// Both the setter and getter acquire the GC lock to avoid data races.
    fn GC_set_stop_func(stop_func: GC_stop_func);
    fn GC_get_stop_func() -> GC_stop_func;

    /// Return the number of bytes in the heap.  Excludes collector private
    /// data structures.  Excludes the unmapped memory (returned to the OS).
    /// Includes empty blocks and fragmentation loss.  Includes some pages
    /// that were allocated but never written.
    /// This is an unsynchronized getter, so it should be called typically
    /// with the GC lock held to avoid data races on multiprocessors (the
    /// alternative is to use GC_get_heap_usage_safe or GC_get_prof_stats
    /// API calls instead).
    /// This getter remains lock-free (unsynchronized) for compatibility
    /// reason since some existing clients call it from a GC callback
    /// holding the allocator lock.  (This API function and the following
    /// four ones bellow were made thread-safe in GC v7.2alpha1 and
    /// reverted back in v7.2alpha7 for the reason described.)
    fn GC_get_heap_size() -> size_t;

    /// Return a lower bound on the number of free bytes in the heap
    /// (excluding the unmapped memory space).  This is an unsynchronized
    /// getter (see GC_get_heap_size comment regarding thread-safety).
    fn GC_get_free_bytes() -> size_t;

    /// Return the size (in bytes) of the unmapped memory (which is returned
    /// to the OS but could be remapped back by the collector later unless
    /// the OS runs out of system/virtual memory). This is an unsynchronized
    /// getter (see GC_get_heap_size comment regarding thread-safety).
    fn GC_get_unmapped_bytes() -> size_t;

    /// Return the number of bytes allocated since the last collection.
    /// This is an unsynchronized getter (see GC_get_heap_size comment
    /// regarding thread-safety).
    fn GC_get_bytes_since_gc() -> size_t;

    /// Return the total number of bytes allocated in this process.
    /// Never decreases, except due to wrapping.  This is an unsynchronized
    /// getter (see GC_get_heap_size comment regarding thread-safety).
    fn GC_get_total_bytes() -> size_t;

    /// Return the heap usage information.  This is a thread-safe (atomic)
    /// alternative for the five above getters.   (This function acquires
    /// the allocator lock thus preventing data racing and returning the
    /// consistent result.)  Passing NULL pointer is allowed for any
    /// argument.  Returned (filled in) values are of word type.
    /// (This API function was introduced in GC v7.2alpha7 at the same time
    /// when GC_get_heap_size and the friends were made lock-free again.)
    fn GC_get_heap_usage_safe(pheap_size: *mut GC_word,
                                  pfree_bytes: *mut GC_word,
                                  punmapped_bytes: *mut GC_word,
                                  pbytes_since_gc: *mut GC_word,
                                  ptotal_bytes: *mut GC_word);

    /// Atomically get GC statistics (various global counters).  Clients
    /// should pass the size of the buffer (of GC_prof_stats_s type) to fill
    /// in the values - this is for interoperability between different GC
    /// versions, an old client could have fewer fields, and vice versa,
    /// client could use newer gc.h (with more entries declared in the
    /// structure) than that of the linked libgc binary; in the latter case,
    /// unsupported (unknown) fields are filled in with -1.  Return the size
    /// (in bytes) of the filled in part of the structure (excluding all
    /// unknown fields, if any).
    fn GC_get_prof_stats(p: *mut GC_prof_stats_s, stats_sz: size_t) -> size_t;

    /// Same as above but unsynchronized (i.e., not holding the allocation
    /// lock).  Clients should call it using GC_call_with_alloc_lock to
    /// avoid data races on multiprocessors.
    fn GC_get_prof_stats_unsafe(p: *mut GC_prof_stats_s, stats_sz: size_t) -> size_t;

    /// Disable garbage collection.  Even GC_gcollect calls will be
    /// ineffective.
    fn GC_disable();

    /// Return non-zero (TRUE) if and only if garbage collection is disabled
    /// (i.e., GC_dont_gc value is non-zero).  Does not acquire the lock.
    fn GC_is_disabled() -> c_int;

    /// Try to re-enable garbage collection.  GC_disable() and GC_enable()
    /// calls nest.  Garbage collection is enabled if the number of calls to
    /// both functions is equal.
    fn GC_enable();

    /// Perform some garbage collection work, if appropriate.
    /// Return 0 if there is no more work to be done.
    /// Typically performs an amount of work corresponding roughly
    /// to marking from one page.  May do more work if further
    /// progress requires it, e.g. if incremental collection is
    /// disabled.  It is reasonable to call this in a wait loop
    /// until it returns 0.
    fn GC_collect_a_little() -> c_int;

    /// Allocate an object of size lb bytes.  The client guarantees that
    /// as long as the object is live, it will be referenced by a pointer
    /// that points to somewhere within the first 256 bytes of the object.
    /// (This should normally be declared volatile to prevent the compiler
    /// from invalidating this assertion.)  This routine is only useful
    /// if a large array is being allocated.  It reduces the chance of
    /// accidentally retaining such an array as a result of scanning an
    /// integer that happens to be an address inside the array.  (Actually,
    /// it reduces the chance of the allocator not finding space for such
    /// an array, since it will try hard to avoid introducing such a false
    /// reference.)  On a SunOS 4.X or MS Windows system this is recommended
    /// for arrays likely to be larger than 100K or so.  For other systems,
    /// or if the collector is not configured to recognize all interior
    /// pointers, the threshold is normally much higher.
    #[cfg(bdw_pristine_api)]
    fn GC_malloc_ignore_off_page(lb: size_t) -> *mut c_void;
    #[cfg(bdw_pristine_api)]
    fn GC_debug_malloc_ignore_off_page(lb: size_t,
                                           file: *c_char, lineno: c_int) -> *mut c_void;
    #[cfg(bdw_pristine_api)]
    fn GC_malloc_atomic_ignore_off_page(lb: size_t) -> *mut c_void;
    #[cfg(bdw_pristine_api)]
    fn GC_debug_malloc_atomic_ignore_off_page(lb: size_t,
                                                  file: *c_char, lineno: c_int) -> *mut c_void;

    /// (only defined if the library has been suitably compiled)
    #[cfg(bdw_pristine_api)]
    fn GC_malloc_atomic_uncollectable(size_in_bytes: size_t) -> *mut c_void;
    fn GC_exchange_malloc_atomic_uncollectable(size_in_bytes: size_t) -> *mut c_void;
    fn GC_proc_malloc_atomic_uncollectable(size_in_bytes: size_t) -> *mut c_void;
    fn GC_other_malloc_atomic_uncollectable(size_in_bytes: size_t) -> *mut c_void;

    /// (only defined if the library has been suitably compiled)
    #[cfg(bdw_pristine_api)]
    fn GC_debug_malloc_atomic_uncollectable(size_in_bytes: size_t,
                                                file: *c_char, lineno: c_int) -> *mut c_void;
    fn GC_debug_exchange_malloc_atomic_uncollectable(size_in_bytes: size_t,
                                                file: *c_char, lineno: c_int) -> *mut c_void;
    fn GC_debug_proc_malloc_atomic_uncollectable(size_in_bytes: size_t,
                                                file: *c_char, lineno: c_int) -> *mut c_void;
    fn GC_debug_other_malloc_atomic_uncollectable(size_in_bytes: size_t,
                                                file: *c_char, lineno: c_int) -> *mut c_void;


    /// When obj is no longer accessible, invoke
    /// (*fn)(obj, cd).  If a and b are inaccessible, and
    /// a points to b (after disappearing links have been
    /// made to disappear), then only a will be
    /// finalized.  (If this does not create any new
    /// pointers to b, then b will be finalized after the
    /// next collection.)  Any finalizable object that
    /// is reachable from itself by following one or more
    /// pointers will not be finalized (or collected).
    /// Thus cycles involving finalizable objects should
    /// be avoided, or broken by disappearing links.
    /// All but the last finalizer registered for an object
    /// is ignored.
    ///
    /// Finalization may be removed by passing 0 as fn.
    /// Finalizers are implicitly unregistered when they are
    /// enqueued for finalization (i.e. become ready to be
    /// finalized).
    ///
    /// The old finalizer and client data are stored in
    /// *ofn and *ocd.  (ofn and/or ocd may be NULL.
    /// The allocation lock is held while *ofn and *ocd are
    /// updated.  In case of error (no memory to register
    /// new finalizer), *ofn and *ocd remain unchanged.)
    /// Fn is never invoked on an accessible object,
    /// provided hidden pointers are converted to real
    /// pointers only if the allocation lock is held, and
    /// such conversions are not performed by finalization
    /// routines.
    ///
    /// If GC_register_finalizer is aborted as a result of
    /// a signal, the object may be left with no
    /// finalization, even if neither the old nor new
    /// finalizer were NULL.
    ///
    /// Obj should be the starting address of an object
    /// allocated by GC_malloc or friends. Obj may also be
    /// NULL or point to something outside GC heap (in this
    /// case, fn is ignored, *ofn and *ocd are set to NULL).
    /// Note that any garbage collectible object referenced
    /// by cd will be considered accessible until the
    /// finalizer is invoked.
    fn GC_register_finalizer(obj: *mut c_void,
                                 fn_: GC_finalization_proc,
                                 cd: *mut c_void,
                                 ofn: *mut GC_finalization_proc,
                                 ocd: *mut *mut c_void);
    fn GC_debug_register_finalizer(obj: *mut c_void,
                                       fn_: GC_finalization_proc,
                                       cd: *mut c_void,
                                       ofn: *mut GC_finalization_proc,
                                       ocd: *mut *mut c_void);

    /// Another versions of the above follow.  It ignores
    /// self-cycles, i.e. pointers from a finalizable object to
    /// itself.  There is a stylistic argument that this is wrong,
    /// but it's unavoidable for C++, since the compiler may
    /// silently introduce these.  It's also benign in that specific
    /// case.  And it helps if finalizable objects are split to
    /// avoid cycles.
    ///
    /// Note that cd will still be viewed as accessible, even if it
    /// refers to the object itself.
    fn GC_register_finalizer_ignore_self(obj: *mut c_void,
                                             fn_: GC_finalization_proc,
                                             cd: *mut c_void,
                                             ofn: *mut GC_finalization_proc,
                                             ocd: *mut *mut c_void);
    fn GC_debug_register_finalizer_ignore_self(obj: *mut c_void,
                                                   fn_: GC_finalization_proc,
                                                   cd: *mut c_void,
                                                   ofn: *mut GC_finalization_proc,
                                                   ocd: *mut *mut c_void);


    /// Another version of the above.  It ignores all cycles.
    /// It should probably only be used by Java implementations.
    /// Note that cd will still be viewed as accessible, even if it
    /// refers to the object itself.
    fn GC_register_finalizer_no_order(obj: *mut c_void,
                                          fn_: GC_finalization_proc,
                                          cd: *mut c_void,
                                          ofn: *mut GC_finalization_proc,
                                          ocd: *mut *mut c_void);
    fn GC_debug_register_finalizer_no_order(obj: *mut c_void,
                                                fn_: GC_finalization_proc,
                                                cd: *mut c_void,
                                                ofn: *mut GC_finalization_proc,
                                                ocd: *mut *mut c_void);

    /// This is a special finalizer that is useful when an object's
    /// finalizer must be run when the object is known to be no
    /// longer reachable, not even from other finalizable objects.
    /// It behaves like "normal" finalization, except that the
    /// finalizer is not run while the object is reachable from
    /// other objects specifying unordered finalization.
    /// Effectively it allows an object referenced, possibly
    /// indirectly, from an unordered finalizable object to override
    /// the unordered finalization request.
    /// This can be used in combination with finalizer_no_order so
    /// as to release resources that must not be released while an
    /// object can still be brought back to life by other
    /// finalizers.
    /// Only works if GC_java_finalization is set.  Probably only
    /// of interest when implementing a language that requires
    /// unordered finalization (e.g. Java, C#).
    fn GC_register_finalizer_unreachable(obj: *mut c_void,
                                             fn_: GC_finalization_proc,
                                             cd: *mut c_void,
                                             ofn: *mut GC_finalization_proc,
                                             ocd: *mut *mut c_void);
    fn GC_debug_register_finalizer_unreachable(obj: *mut c_void,
                                                   fn_: GC_finalization_proc,
                                                   cd: *mut c_void,
                                                   ofn: *mut GC_finalization_proc,
                                                   ocd: *mut *mut c_void);


    /// The following routine may be used to break cycles between
    /// finalizable objects, thus causing cyclic finalizable
    /// objects to be finalized in the correct order.  Standard
    /// use involves calling GC_register_disappearing_link(&p),
    /// where p is a pointer that is not followed by finalization
    /// code, and should not be considered in determining
    /// finalization order.
    ///
    /// Link should point to a field of a heap allocated
    /// object obj.  *link will be cleared when obj is
    /// found to be inaccessible.  This happens BEFORE any
    /// finalization code is invoked, and BEFORE any
    /// decisions about finalization order are made.
    /// This is useful in telling the finalizer that
    /// some pointers are not essential for proper
    /// finalization.  This may avoid finalization cycles.
    /// Note that obj may be resurrected by another
    /// finalizer, and thus the clearing of *link may
    /// be visible to non-finalization code.
    /// There's an argument that an arbitrary action should
    /// be allowed here, instead of just clearing a pointer.
    /// But this causes problems if that action alters, or
    /// examines connectivity.  Returns GC_DUPLICATE if link
    /// was already registered, GC_SUCCESS if registration
    /// succeeded, GC_NO_MEMORY if it failed for lack of
    /// memory, and GC_oom_fn did not handle the problem.
    /// Only exists for backward compatibility.  See below:
    fn GC_register_disappearing_link(link: *mut *mut c_void) -> c_int;

    /// A slight generalization of the above. *link is
    /// cleared when obj first becomes inaccessible.  This
    /// can be used to implement weak pointers easily and
    /// safely. Typically link will point to a location
    /// holding a disguised pointer to obj.  (A pointer
    /// inside an "atomic" object is effectively disguised.)
    /// In this way, weak pointers are broken before any
    /// object reachable from them gets finalized.
    /// Each link may be registered only with one obj value,
    /// i.e. all objects but the last one (link registered
    /// with) are ignored.  This was added after a long
    /// email discussion with John Ellis.
    /// link must be non-NULL (and be properly aligned).
    /// obj must be a pointer to the first word of an object
    /// allocated by GC_malloc or friends.  It is unsafe to
    /// explicitly deallocate the object containing link.
    /// Explicit deallocation of obj may or may not cause
    /// link to eventually be cleared.
    /// This function can be used to implement certain types
    /// of weak pointers.  Note, however, this generally
    /// requires that the allocation lock is held (see
    /// GC_call_with_alloc_lock() below) when the disguised
    /// pointer is accessed.  Otherwise a strong pointer
    /// could be recreated between the time the collector
    /// decides to reclaim the object and the link is
    /// cleared.  Returns GC_SUCCESS if registration
    /// succeeded (a new link is registered), GC_DUPLICATE
    /// if link was already registered (with some object),
    /// GC_NO_MEMORY if registration failed for lack of
    /// memory (and GC_oom_fn did not handle the problem).
    fn GC_general_register_disappearing_link(link: *mut *mut c_void,
                                                 obj: *c_void) -> c_int;

    /// Moves a link previously registered via
    /// GC_general_register_disappearing_link (or
    /// GC_register_disappearing_link).  Does not change the
    /// target object of the weak reference.  Does not
    /// change (*new_link) content.  May be called with
    /// new_link equal to link (to check whether link has
    /// been registered).  Returns GC_SUCCESS on success,
    /// GC_DUPLICATE if there is already another
    /// disappearing link at the new location (never
    /// returned if new_link is equal to link), GC_NOT_FOUND
    /// if no link is registered at the original location.
    fn GC_move_disappearing_link(link: *mut *mut c_void,
                                     new_link: *mut *mut c_void) -> c_int;

    /// Undoes a registration by either of the above two
    /// routines.  Returns 0 if link was not actually
    /// registered (otherwise returns 1).
    fn GC_unregister_disappearing_link(arg1: *mut *mut c_void) -> c_int;

    /// Similar to GC_general_register_disappearing_link but
    /// *link only gets cleared when obj becomes truly
    /// inaccessible.  An object becomes truly inaccessible
    /// when it can no longer be resurrected from its
    /// finalizer (e.g. by assigning itself to a pointer
    /// traceable from root).  This can be used to implement
    /// long weak pointers easily and safely.
    fn GC_register_long_link(link: *mut *mut c_void, obj: *c_void) -> c_int;

    /// Similar to GC_move_disappearing_link but for a link
    /// previously registered via GC_register_long_link.
    fn GC_move_long_link(link: *mut *mut c_void, new_link: *mut *mut c_void) -> c_int;

    /// Similar to GC_unregister_disappearing_link but for a
    /// registration by either of the above two routines.
    fn GC_unregister_long_link(link: *mut *mut c_void) -> c_int;

    /// Returns !=0 if GC_invoke_finalizers has something to do.
    fn GC_should_invoke_finalizers() -> c_int;

    /// Run finalizers for all objects that are ready to
    /// be finalized.  Return the number of finalizers
    /// that were run.  Normally this is also called
    /// implicitly during some allocations.  If
    /// GC_finalize_on_demand is nonzero, it must be called
    /// explicitly.
    fn GC_invoke_finalizers() -> c_int;

    /// GC_set_warn_proc can be used to redirect or filter warning messages.
    /// p may not be a NULL pointer.  msg is printf format string (arg must
    /// match the format).  Both the setter and the getter acquire the GC
    /// lock (to avoid data races).
    fn GC_set_warn_proc(p: GC_warn_proc);

    /// GC_get_warn_proc returns the current warn_proc.
    fn GC_get_warn_proc() -> GC_warn_proc;

    /// GC_ignore_warn_proc may be used as an argument for GC_set_warn_proc
    /// to suppress all warnings (unless statistics printing is turned on).
    fn GC_ignore_warn_proc(arg1: *mut c_char, arg2: GC_word);

    /// abort_func is invoked on GC fatal aborts (just before OS-dependent
    /// abort or exit(1) is called).  Must be non-NULL.  The default one
    /// outputs msg to stderr provided msg is non-NULL.  msg is NULL if
    /// invoked before exit(1) otherwise msg is non-NULL (i.e., if invoked
    /// before abort).  Both the setter and getter acquire the GC lock.
    /// Both the setter and getter are defined only if the library has been
    /// compiled without SMALL_CONFIG.
    fn GC_set_abort_func(abort_func: GC_abort_func);
    fn GC_get_abort_func() -> GC_abort_func;

    fn GC_call_with_alloc_lock(fn_: GC_fn_type, client_data: *mut c_void) -> *mut c_void;

    /// These routines are intended to explicitly notify the collector
    /// of new threads.  Often this is unnecessary because thread creation
    /// is implicitly intercepted by the collector, using header-file
    /// defines, or linker-based interception.  In the long run the intent
    /// is to always make redundant registration safe.  In the short run,
    /// this is being implemented a platform at a time.
    ///
    /// The interface is complicated by the fact that we probably will not
    /// ever be able to automatically determine the stack base for thread
    /// stacks on all platforms.

    /// Call a function with a stack base structure corresponding to
    /// somewhere in the GC_call_with_stack_base frame.  This often can
    /// be used to provide a sufficiently accurate stack base.  And we
    /// implement it everywhere.
    fn GC_call_with_stack_base(fn_: GC_stack_base_func, arg: *mut c_void) -> *mut c_void;

    /// Suggest the GC to use the specific signal to suspend threads.
    /// Has no effect after GC_init and on non-POSIX systems.
    fn GC_set_suspend_signal(signal: c_int);

    /// Suggest the GC to use the specific signal to resume threads.
    /// Has no effect after GC_init and on non-POSIX systems.
    fn GC_set_thr_restart_signal(signal: c_int);

    /// Return the signal number (constant after initialization) used by
    /// the GC to suspend threads on POSIX systems.  Return -1 otherwise.
    fn GC_get_suspend_signal() -> c_int;

    /// Return the signal number (constant after initialization) used by
    /// the garbage collector to restart (resume) threads on POSIX
    /// systems.  Return -1 otherwise.
    fn GC_get_thr_restart_signal() -> c_int;

    /// Restart marker threads after POSIX fork in child.  Meaningless in
    /// other situations.  Should not be called if fork followed by exec.
    fn GC_start_mark_threads();

    /// Explicitly enable GC_register_my_thread() invocation.
    /// Done implicitly if a GC thread-creation function is called (or
    /// implicit thread registration is activated, or the collector is
    /// compiled with GC_ALWAYS_MULTITHREADED defined).  Otherwise, it
    /// must be called from the main (or any previously registered) thread
    /// between the collector initialization and the first explicit
    /// registering of a thread (it should be called as late as possible).
    fn GC_allow_register_threads();

    /// Register the current thread, with the indicated stack base, as
    /// a new thread whose stack(s) should be traced by the GC.  If it
    /// is not implicitly called by the GC, this must be called before a
    /// thread can allocate garbage collected memory, or assign pointers
    /// to the garbage collected heap.  Once registered, a thread will be
    /// stopped during garbage collections.
    ///
    /// This call must be previously enabled (see above).
    /// This should never be called from the main thread, where it is
    /// always done implicitly.  This is normally done implicitly if GC_
    /// functions are called to create the thread, e.g. by including gc.h
    /// (which redefines some system functions) before calling the system
    /// thread creation function.  Nonetheless, thread cleanup routines
    /// (eg., pthread key destructor) typically require manual thread
    /// registering (and unregistering) if pointers to GC-allocated
    /// objects are manipulated inside.
    ///
    /// It is also always done implicitly on some platforms if
    /// GC_use_threads_discovery() is called at start-up.  Except for the
    /// latter case, the explicit call is normally required for threads
    /// created by third-party libraries.
    ///
    /// A manually registered thread requires manual unregistering.
    fn GC_register_my_thread(sb: *Struct_GC_stack_base) -> c_int;

    /// Return non-zero (TRUE) if and only if the calling thread is
    /// registered with the garbage collector.
    fn GC_thread_is_registered() -> c_int;

    /// Unregister the current thread.  Only an explicitly registered
    /// thread (i.e. for which GC_register_my_thread() returns GC_SUCCESS)
    /// is allowed (and required) to call this function.  (As a special
    /// exception, it is also allowed to once unregister the main thread.)
    /// The thread may no longer allocate garbage collected memory or
    /// manipulate pointers to the garbage collected heap after making
    /// this call.  Specifically, if it wants to return or otherwise
    /// communicate a pointer to the garbage-collected heap to another
    /// thread, it must do this before calling GC_unregister_my_thread,
    /// most probably by saving it in a global data structure.  Must not
    /// be called inside a GC callback function (except for
    /// GC_call_with_stack_base() one).
    fn GC_unregister_my_thread() -> c_int;

    /// Wrapper for functions that are likely to block (or, at least, do not
    /// allocate garbage collected memory and/or manipulate pointers to the
    /// garbage collected heap) for an appreciable length of time.  While fn
    /// is running, the collector is said to be in the "inactive" state for
    /// the current thread (this means that the thread is not suspended and
    /// the thread's stack frames "belonging" to the functions in the
    /// "inactive" state are not scanned during garbage collections).  It is
    /// allowed for fn to call GC_call_with_gc_active() (even recursively),
    /// thus temporarily toggling the collector's state back to "active".
    fn GC_do_blocking(fn_: GC_fn_type, client_data: *mut c_void) -> *mut c_void;

    /// Call a function switching to the "active" state of the collector for
    /// the current thread (i.e. the user function is allowed to call any
    /// GC function and/or manipulate pointers to the garbage collected
    /// heap).  GC_call_with_gc_active() has the functionality opposite to
    /// GC_do_blocking() one.  It is assumed that the collector is already
    /// initialized and the current thread is registered.  fn may toggle
    /// the collector thread's state temporarily to "inactive" one by using
    /// GC_do_blocking.  GC_call_with_gc_active() often can be used to
    /// provide a sufficiently accurate stack base.
    fn GC_call_with_gc_active(fn_: GC_fn_type, client_data: *mut c_void) -> *mut c_void;

    /// Attempt to fill in the GC_stack_base structure with the stack base
    /// for this thread.  This appears to be required to implement anything
    /// like the JNI AttachCurrentThread in an environment in which new
    /// threads are not automatically registered with the collector.
    /// It is also unfortunately hard to implement well on many platforms.
    /// Returns GC_SUCCESS or GC_UNIMPLEMENTED.  This function acquires the
    /// GC lock on some platforms.
    fn GC_get_stack_base(arg1: *mut Struct_GC_stack_base) -> c_int;

    /// Check that p is visible to the collector as a possibly pointer
    /// containing location.  If it isn't fail conspicuously.
    ///
    /// Returns the argument in all cases.  May erroneously succeed
    /// in hard cases.  (This is intended for debugging use with
    /// untyped allocations.  The idea is that it should be possible, though
    /// slow, to add such a call to all indirect pointer stores.)
    /// Currently useless for multi-threaded worlds.
    fn GC_is_visible(arg1: *mut c_void) -> *mut c_void;

    /// Check that if p is a pointer to a heap page, then it points to
    /// a valid displacement within a heap object.
    ///
    /// Fail conspicuously if this property does not hold.
    /// Uninteresting with GC_all_interior_pointers.
    /// Always returns its argument.
    fn GC_is_valid_displacement(arg1: *mut c_void) -> *mut c_void;

    /// Explicitly dump the GC state.  This is most often called from the
    /// debugger, or by setting the GC_DUMP_REGULARLY environment variable,
    /// but it may be useful to call it from client code during debugging.
    /// Defined only if the library has been compiled without NO_DEBUGGING.
    fn GC_dump();

    /// We need to intercept calls to many of the threads primitives, so
    /// that we can locate thread stacks and stop the world.
    /// Note also that the collector cannot always see thread specific data.
    /// Thread specific data should generally consist of pointers to
    /// uncollectible objects (allocated with GC_malloc_uncollectable,
    /// not the system malloc), which are deallocated using the destructor
    /// facility in thr_keycreate.  Alternatively, keep a redundant pointer
    /// to thread specific data on the thread stack.

    fn GC_dlopen(path: *c_char, mode: c_int) -> *c_void;
    fn GC_pthread_sigmask(how: c_int, sigset: *sigset_t, oset: *mut sigset_t) -> c_int;

    fn GC_pthread_create(t: *mut pthread_t, attr: *pthread_attr_t,
                         start: thread::StartFn, value: *c_void) -> c_int;
    // FIXME #11542: (shouldn't retval be *mut *mut c_void, or
    // at least *mut *c_void?  But thread.rs declares it as **c_void...)
    fn GC_pthread_join(t: pthread_t, retval: **c_void) -> c_int;
    fn GC_pthread_detach(t: pthread_t) -> c_int;
    fn GC_pthread_cancel(t: pthread_t) -> c_int;
    fn GC_pthread_exit(value_ptr: *mut c_void) -> !;

    /// This returns a list of objects, linked through their first word.
    /// Its use can greatly reduce lock contention problems, since the
    /// allocation lock can be acquired and released many fewer times.
    fn GC_malloc_many(lb: size_t) -> *mut c_void;

    /// Register a new callback (a user-supplied filter) to control the
    /// scanning of dynamic libraries.  Replaces any previously registered
    /// callback.  May be 0 (means no filtering).  May be unused on some
    /// platforms (if the filtering is unimplemented or inappropriate).
    fn GC_register_has_static_roots_callback(f: GC_has_static_roots_func);

    /// Public setter and getter for switching "unmap as much as possible"
    /// mode on(1) and off(0).  Has no effect unless unmapping is turned on.
    /// Has no effect on implicitly-initiated garbage collections.  Initial
    /// value is controlled by GC_FORCE_UNMAP_ON_GCOLLECT.  The setter and
    /// getter are unsynchronized.
    fn GC_set_force_unmap_on_gcollect(flag: c_int);
    fn GC_get_force_unmap_on_gcollect() -> c_int;

}

#[cfg(test)]
mod test {

    #[test]
    fn gc_smoke_test() {

    }

}
