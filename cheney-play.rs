#[feature(managed_boxes)];
#[allow(dead_code)]; // reenable check after done with dev.
#[allow(unused_imports)];
use std::cast;
use std::mem;
use std::ptr;
use RawBox = std::unstable::raw::Box;
use std::rt::global_heap;
use std::unstable::intrinsics;
use std::unstable::intrinsics::{TyDesc};

// Reminder:
// struct Box<T> {
//    ref_count: uint, type_desc: *TyDesc,
//    prev: *mut Box<T>, next: *mut Box<T>, data: T }

/// A Span holds the span `[start, limit)` for contiguous area of memory.
struct Span {
    start: *uint, // address of first word of the span's memory.
    limit: *uint, // address immediately after last word in span's memory.
}

impl Span {
    fn new(start: *uint, limit: *uint) -> Span{
        let ret = Span{ start: start, limit: limit };
        debug!("Span::new({}, {})", start, limit);
        ret
    }
    fn tup(&self) -> (*uint, *uint) { (self.start, self.limit) }
    fn from((start, limit): (*uint, *uint)) -> Span { Span::new(start, limit) }
    fn size_bytes(&self) -> uint { (self.limit as uint) - (self.start as uint) }
    fn can_fit(&self, bytes: uint) -> bool { bytes <= self.size_bytes() }
    fn would_exhaust(&self, bytes: uint) -> bool { ! self.can_fit(bytes) }
    unsafe fn shift_start(&mut self, bytes: uint) {
        assert!(self.can_fit(bytes));
        assert!(bytes as int >= 0);
        self.start = ptr::offset(self.start as *u8, bytes as int) as *uint;
    }
}

/// A Chunk is the metadata for a contiguous area of memory that has
/// been individually allocated, and that can be individually freed
/// when it is safe to do so (i.e. when it contains no live objects).

static DEFAULT_CHUNK_SIZE: uint = 1_000_000; // 1 megabyte.
struct Chunk {
    next: Option<*Chunk>, // next chunk in this collection.
    free_pairs: Option<*FreePair>,
    free_bblks: Option<*BigBlock>,
    full_bblks: Option<*BigBlock>,
    span: Span, // span covered by chunk's memory.
}

impl Chunk {

    fn new_default() -> Chunk { Chunk::new(DEFAULT_CHUNK_SIZE) }

    /// Allocates memory for a chunk (via `malloc`) and sets it up
    /// as one large BigBlock in the Chunk.
    fn new(size: uint) -> Chunk {

        // ensure we can safely do desired casts to block types.
        assert!(size >= mem::size_of::<FreePair>());
        assert!(size >= mem::size_of::<BigBlock>());
        assert!(size >= mem::size_of::<FutureBox<()>>());
        assert!(size >= mem::size_of::<ForwardedBox<()>>());

        let word_size = mem::size_of::<uint>();
        if 0 != size % word_size {
            fail!("chunks must be multiples of machine words.");
        }

        unsafe {
            let chunk_mem = global_heap::malloc_raw(size);
            let start : *uint = cast::transmute(chunk_mem);
            assert!((size as int) >= 0);
            let limit : *uint = ptr::offset(start, (size / word_size) as int);
            let block : *mut BigBlock = cast::transmute(start);
            (*block).next = ptr::null();
            (*block).limit = limit;
            Chunk {
                next: None,
                free_pairs: None,
                free_bblks: Some(cast::transmute(block)),
                full_bblks: None,
                span: Span::new(start, limit),
            }
        }
    }

    /// Pops first free big block and returns its span (presumably for
    /// use as a target allocation space by a bump-pointer allocator).
    unsafe fn unwrap_target_space(&mut self) -> Span {
        let b : *BigBlock = self.free_bblks.unwrap();
        self.free_bblks =
            if (*b).next == ptr::null() { None } else { Some((*b).next) };
        let start : *uint = cast::transmute(b);
        let limit = (*b).limit;
        Span::new(start, limit)
    }

    unsafe fn free_all(&mut self) {
        use std::libc;
        let mut ptr   = self.span.start;
        let mut next  = self.next;
        loop {
            global_heap::free_raw(ptr as *libc::c_void);
            match next {
                None => break,
                Some(p) => { ptr = (*p).span.start; next = (*p).next; }
            }
        }
    }
}

/// A Block is a contiguous slice of memory within a Chunk.  When
/// unallocated by the mutator (i.e. "free"), blocks can carry
/// meta-data (given below).  Free blocks can be broken up into
/// subblocks in order to satisfy smaller memory requests.
///
/// There are two kinds of Blocks:
/// - a Pair is a 2 word Block.  This is the minimum block size.
/// - a BigBlock is a Block of >= 4 words.  It carries its size.
///
/// BigBlocks can always be broken into subblocks as necessary, down
/// to the minimum block size.  Of course, this can fragment the heap.

struct FreePair {
    next: *FreePair, // next block in (free-pairs, chunk).
}

struct FutureBox<T> {
    type_desc: *TyDesc,
    data: T,
}

struct ForwardedBox<T> {
    type_desc: *TyDesc,
    forwarding_address: *FutureBox<T>,
}

enum BlockCategory { Empty, Full, InUse, }

/// Every BigBlock implicitly belongs to some BlockCategory.
struct BigBlock {
    next: *BigBlock, // next block in (free-big-blocks, chunk).
    limit: *uint,    // address immediately after last word in block.
}

static MINIMUM_TARGET_SIZE: uint = DEFAULT_CHUNK_SIZE;
static DEFAULT_LOAD_FACTOR: f32 = 3.0;
static INITIAL_FAKE_REF_COUNT: uint = 2;
struct Gc {
    normal_chunks: Chunk,
    large_objects: Option<*Chunk>,
    /// Our last measured amount of space occupied by objects in normal_chunks.
    last_live_normal_size: uint,
    /// Our last measured amount of space occupied by objects in large_objects.
    last_live_large_size: uint,
    inverse_load_factor: f32,
    target_normal_size: uint,
    target_total_size: uint,
    avail: Span, // span currently in use for bump-pointer allocation
}

impl Gc {
    pub fn make_gc() -> Gc {
        let mut chunk = Chunk::new_default();
        unsafe {
            Gc { normal_chunks: chunk,
                 large_objects: None,
                 last_live_normal_size: 0,
                 last_live_large_size: 0,
                 inverse_load_factor: DEFAULT_LOAD_FACTOR,
                 target_normal_size: MINIMUM_TARGET_SIZE,
                 target_total_size: MINIMUM_TARGET_SIZE,
                 avail: chunk.unwrap_target_space() }
        }
    }

    pub fn alloc<T>(&mut self, arg:T) -> @T {
        unsafe {
            let tydesc = intrinsics::get_tydesc::<T>();
            let obj = self.alloc_ty_instance(tydesc);
            let obj : *mut RawBox<T> = cast::transmute(obj);
            // artificially pump up ref-count so that cheney will manage this object.

            // Note that a ref_count of `1` does not appear
            // sufficient; probably because this code is almost
            // certainly decrementing the ref-count when it returns
            // the transmuted box below, and thus ... enqueuing it for
            // freeing?  Odd though, I would have thought such a bug
            // would cause problems sooner than the task shutdown.

            (*obj).ref_count = INITIAL_FAKE_REF_COUNT;
            (*obj).type_desc = tydesc;
            (*obj).prev = ptr::mut_null();
            (*obj).next = ptr::mut_null();
            (*obj).data = arg;
            let obj : @T = cast::transmute(obj);
            return obj;
        }
    }

    unsafe fn alloc_ty_instance(&mut self, tydesc: *TyDesc) -> *uint {
        let total_size = global_heap::get_box_size((*tydesc).size, (*tydesc).align);
        if self.avail.would_exhaust(total_size) {
            // TODO: if total_size is large enough, consider
            // allocating a separate chunk for it rather than
            // immediately jumping into a Gc attempt.

            self.fill_remaining_space();
            self.perform_collection();
        }
        assert!(self.avail.can_fit(total_size));
        let result = self.avail.start;
        self.avail.shift_start(total_size);
        return result;
    }

    fn fill_remaining_space(&mut self) {
        // TODO: inject placeholder object with fixed-size header as
        // to spend O(1) effort rather than O(|remainingspace|).
        let mut a = self.avail.start;
        let lim = self.avail.limit;
        println!("fill_remaining_space: a: {} lim: {} lim-a: {} bytes",
               a, lim, (lim as uint) - (a as uint));
        unsafe {
            while a < lim {
                {
                    let a : *mut uint = cast::transmute(a);
                    *a = 0;
                }
                a = ptr::offset(a, 1);
            }
            self.avail.start = lim;
        }
    }

    fn perform_collection(&mut self) {
        #[allow(unused_variable)];

        let owned_objects_to_scan : ~[*()] = ~[];
        let pinned_shared_to_scan : ~[*RawBox<()>] = ~[];
        let scan_ptr : *uint;
        let to_ptr : *uint;
        let limit  : *uint;

        // XXX: worrisome potential for wasted effort on duplicate
        // entries in owned_objects_to_scan.  Perhaps consider keeping
        // a mark-bit (somewhere) for this.  (However, this approach
        // should be *sound*, just asympotically inefficient.)

        // XXX: more worrisome: we cannot map a untyped pointer to an
        // owned object (interior or not) to its meta-data (e.g. its
        // size and layout).

        // 1. Traverse objects immediately reachable via the roots
        //    (including stack).
        //    Enqueue owned objects immediately reachable from roots into
        //    `owned_objects_to_scan`.
        //    Pin shared objects immediately reachable from roots and
        //    enqueue them into `pinned_shared_to_scan`.
        //
        // 2. While `owned_objects_to_scan` non-empty:
        //    2a. Pop an object O from owned_objects_to_scan
        //    2b. Enqueue owned objects immediately reachable from O into
        //        `owned_objects_to_scan`.
        //    2c. Pin shared objects immediately reachable from O and
        //        enqueue them into `pinned_shared_to_scan`.
        //
        // 3. (TODO: make policy decision here as to whether to do copying-
        //     or mark-sweep GC, based on variables such as how much of the
        //     existing chunks have been pinned, how fragmented the heap is,
        //     or how much of our heap is non-resident memory.)
        //
        // 4. Loop until `pinned_to_scan` empty and `scan_ptr == to_ptr`.
        //    4a. Scan `pinned_to_scan`, forwarding to `to_space`, and
        //    4b. scan all in span (scan_ptr, to_ptr].
        //
        // Scanning an object means traversing its member fields: for
        // each @T
        // any unpinned refere
        //
        // If during ever during a forwarding attempt above we have
        // `to_ptr == limit`, then must find a to_space (either in the
        // free_bblks of the Gc's chunks, or by allocating a fresh
        // chunk).

    }

    /// Returns total size of space occupied by normal_chunks.
    fn normal_chunks_size(&self) -> uint {
        let mut accum = 0;
        let l : Option<*Chunk> = Some(&self.normal_chunks as *Chunk);
        loop {
            match l {
                None => break,
                Some(c) => accum += unsafe { (*c).span.size_bytes() } }
        }
        return accum;
    }
}

fn main() {
    println!("Hello world.");
    let mut gc = Gc::make_gc();
    enum Pair<T> { Cons(T, @Pair<T>), Null }
    let i3 = gc.alloc::<int>(3);
    println!("i3: {:?}", i3);
}

impl Drop for Gc {
    fn drop(&mut self) {
        unsafe {
            self.normal_chunks.free_all();
            match self.large_objects.take() {
                None => {}, Some(c) => {
                    let c : *mut Chunk = cast::transmute(c);
                    (*c).free_all()
                }
            }
        }
    }
}
