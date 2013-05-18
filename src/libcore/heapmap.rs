// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.


//! Heap allocation and GC mark-bit accounting data structures.
//!
//! Structures in this module are concerned with keeping track
//! of a large number of allocations: those covering the local
//! heap of each task.
//!
//! This module does not (at the time of this writing) contain
//! logic for efficiently locating free regions within a page
//! or moving values during GC. It could grow these capabilities
//! over time, but at the moment it assumes a lower-level allocator
//! such as malloc is _producing_ the allocations. This module just
//! contains structures to help index those allocations for the
//! sake of garbage collecting them.

#[deny(managed_heap_memory)];

use uint;
use trie::TrieMap;
use container::Map;
use option::{Some,None};

/// log_2(pagesize). On windows, pages are 64k. On most unixes they're
/// usually 4k. So these are 16 and 12 respectively.
///
/// Note: it is not presently necessary for page size to actually be
/// the size of an OS-page, though they are set that way as a first
/// approximation, and a few things may break if you pick a
/// non-power-of-2.
///
/// It is also _likely_ that we will keep these at OS page sizes
/// as we are likely to transition this map to managing the local
/// heap on its own, rather than layering on top of malloc. At
/// that point the size may become mandatory.
///
/// Synthetic tests suggest that it does not matter _that_ much
/// whether we pick 4k or 64k pages for this; real-world tests may
/// reveal a different answer.
#[cfg(target_os="win32")]
static BYTES_PER_PAGE_LOG2 : uint = 16;
#[not(cfg(target_os="win32"))]
static BYTES_PER_PAGE_LOG2 : uint = 12;

static BYTES_PER_PAGE : uint = 1 << BYTES_PER_PAGE_LOG2;
static PAGE_MASK : uint = BYTES_PER_PAGE - 1;

/// Page contents are tracked in terms of cells, not bytes. A cell is
/// the smallest unit you can get back from the underlying allocator
/// and/or natural unit of alignment for allocations. It is, in any
/// case, the smallest unit we track allocated-ness / free-ness in
/// terms of. This is set to 8 bytes presently, but it might need
/// per-platform or per-underlying-malloc adjustment.
static BYTES_PER_CELL_LOG2 : uint = 3;
static BYTES_PER_CELL : uint = 1 << BYTES_PER_CELL_LOG2;
static CELLS_PER_PAGE : uint = BYTES_PER_PAGE >> BYTES_PER_CELL_LOG2;

/// A cell can assume 4 states (see `CellState`) so it is mapped
/// in this structure using 2 bits.
static BITS_PER_CELL_MAP : uint = 2;

/// A cell can be in 4 states: `CELL_EMPTY`, `CELL_BEGIN_BLACK`,
/// `CELL_BEGIN_WHITE`, and `CELL_CONTD`. An allocation is represented
/// by one `BEGIN_*` cell followed by 0 or more `CELL_CONTD` cells.
/// Unallocated space is represented by `CELL_EMPTY`.
type CellState = u8;
static CELL_EMPTY : CellState = 0b00;
static CELL_BEGIN_WHITE : CellState = 0b01;
static CELL_BEGIN_BLACK : CellState = 0b10;
static CELL_CONTD : CellState = 0b11;
static CELL_MASK : uint = 0b11;

static BITS_PER_PAGE_MAP : uint = BITS_PER_CELL_MAP * CELLS_PER_PAGE;
static UINTS_PER_PAGE_MAP : uint = BITS_PER_PAGE_MAP / uint::bits;

static WORD_MASK : uint = uint::bits - 1;

#[cfg(target_word_size="32")]
static BITS_PER_WORD_LOG2 : uint = 5;

#[cfg(target_word_size="64")]
static BITS_PER_WORD_LOG2 : uint = 6;


/// Logical container for a large set of `(pos,len)` pairs, each
/// representing an allocation `[pos, pos+len)`. For each such
/// allocation, also maintains a mark bit that is set during GC to
/// either black (reachable) or white (unreachable).
///
/// Physically, a facade for two separate containers.
///
///   - `paged_allocs` maps page numbers to `PageMap`s, and contains
///     any allocation that fits within a page. _All_ the allocations
///     that occur on a given page are tracked by a _single_ `PageMap`
///     entry in `paged_allocs`.
///
///   - `extra_allocs` maps addresses to `HeapRecord`s directly.
///     _Each_ allocation stored this way is represented by a
///     _separate_ entry in `extra_allocs`.
///
/// This organization is a bet on space efficiency: we are betting
/// that size and spatial locality of allocations means many of them
/// cluster onto single pages and can be tracked by a smaller number
/// of overall bytes using `PageMap`s than if represented separately
/// as `HeapRecord`s. A `PageMap` is relatively dense under conditions
/// of high spatial locality and small allocations: Between (0.25 *
/// len) and 1024 bits per allocation, in the leaves of the page
/// trie. By contrast, `extra_allocs` costs between 256 and 4096
/// bits per allocation in the leaves of the allocation trie, with
/// many more interior nodes besides.
///
/// It is correct therefore to view `paged_allocs` as a
/// manually-compressed form of the same information that would be
/// stored in `extra_allocs`. Indeed, initial versions of the GC only
/// used a single `TrieMap` like `extra_allocs`, but it was very
/// space-costly.
///
/// The interface to `HeapMap` should present the operations that the
/// GC requires from a _single_ allocation index, and attempt to
/// service the operations by delegating to `paged_allocs` when
/// possible, `extra_allocs` only when necessary.

pub struct HeapMap {
    priv len: uint,
    priv paged_allocs: TrieMap<~PageMap>,
    priv extra_allocs: TrieMap<HeapRecord>
}

impl HeapMap {
    fn new() -> HeapMap {
        HeapMap {
            len: 0,
            paged_allocs: TrieMap::new(),
            extra_allocs: TrieMap::new()
        }
    }

    fn page_num(pos: uint) -> uint {
        pos >> BYTES_PER_PAGE_LOG2
    }

    fn is_subpage_alloc(pos: uint, len: uint) -> bool {
        HeapMap::page_num(pos) == HeapMap::page_num(pos+len)
    }

    fn min_and_max_addrs(&self) -> (uint, uint) {
        let mut min = match self.extra_allocs.next(0) {
            None => 0,
            Some((k, _)) => k
        };
        let mut max = match self.extra_allocs.prev(uint::max_value) {
            None => uint::max_value,
            Some((k, r)) => k + r.size
        };

        min = match self.paged_allocs.next(0) {
            None => min,
            Some((k, _)) => min.min(&(k * BYTES_PER_PAGE))
        };
        let mut max = match self.paged_allocs.prev(uint::max_value) {
            None => max,
            Some((k, _)) => max.max(&((k+1) * BYTES_PER_PAGE))
        };
        return (min, max);        
    }

    fn len(&self) -> uint { self.len }

    fn contains_key(&self, x: &uint) -> bool {
        self.extra_allocs.contains_key(x) ||
            self.paged_allocs_contains_key(x)
    }

    fn paged_allocs_contains_key(&self, x: &uint) -> bool {
        let page_num = HeapMap::page_num(*x);
        match self.paged_allocs.find(&page_num) {
            None => false,
            Some(ref pm) => pm.contains_alloc_starting_at_addr(*x)
        }
    }

    fn each_key(&mut self, f: &fn(&uint) -> bool) -> bool {
        self.extra_allocs.each_key(f);
            
        for self.paged_allocs.mutate_values |pagenum, pm| {
            let base = pagenum * BYTES_PER_PAGE;
            for pm.mutate_values(base) |pos, _, _| {
                if ! f(pos) {
                    return false;
                }
            };
        }
        return true;
    }

    fn mutate_values(&mut self, f: &fn(&uint, &mut HeapRecord) -> bool) -> bool {
        self.extra_allocs.mutate_values(f);
        for self.paged_allocs.mutate_values |pagenum, pm| {
            let base = pagenum * BYTES_PER_PAGE;
            for pm.mutate_values(base) |pos, len, is_marked| {
                let mut hr = HeapRecord {
                    size: *len,
                    is_marked: *is_marked
                };
                if ! f(pos, &mut hr) {
                    return false;
                }
                *is_marked = hr.is_marked;
            };
        }
        return true;
    }

    fn clear_marks_and_enumerate_unmarked(&mut self,
                                          f: &fn(uint,uint) -> bool) -> bool {
        for self.mutate_values |pos, hr| {
            if hr.is_marked {
                if !f(*pos, hr.size) {
                    return false;
                }
            }
            hr.is_marked = false;
        }
    }


    fn mutate_prev(&mut self, addr: uint, f: &fn(uint, &mut HeapRecord)) {
        // Pointer could be anything, we only call back if we find it.
        let page_num = HeapMap::page_num(addr);
        match self.paged_allocs.find_mut(&page_num) {
            Some(pm) => {
                let (state, pos, len) = pm.find_alloc_pos_len(addr);
                assert!(state != CELL_CONTD);
                if state != CELL_EMPTY {
                    let marked = state == CELL_BEGIN_BLACK;
                    let mut hr = HeapRecord {
                        size: len,
                        is_marked: marked
                    };
                    f(pos, &mut hr);
                    if hr.is_marked != marked {
                        pm.set_cell(PageMap::cell_of_addr(pos),
                                    if hr.is_marked {
                                        CELL_BEGIN_BLACK
                                    } else {
                                        CELL_BEGIN_WHITE
                                    });
                    }
                    return;
                }
            }
            None => ()
        }

        // Didn't find it in the page_map, try the trie map.
        self.extra_allocs.mutate_prev(addr, f);
    }

    fn insert(&mut self, pos: &uint, len: &uint) {
        let (pos, len) = (*pos, *len);
        if HeapMap::is_subpage_alloc(pos, len) {
            let page_num = HeapMap::page_num(pos);
            debug!("inserting %x + %u into page map at page %x, offset %u",
                   pos, len, page_num, pos & PAGE_MASK);
            let mut hit = false;
            match self.paged_allocs.find_mut(&page_num) {
                Some(pm) => {
                    pm.add_alloc(pos, len);
                    hit = true;
                }
                None => ()
            }
            if hit {
                self.len += 1;
                return
            }
            let mut pm = ~PageMap::new();
            pm.add_alloc(pos, len);
            self.paged_allocs.insert(page_num, pm);
        } else {
            debug!("inserting %x + %u into trie map",
                   pos, len);
            let hr = HeapRecord {
                size: len,
                is_marked: false
            };
            self.extra_allocs.insert(pos, hr);
            self.len += 1;
        }
    }

    fn remove(&mut self, pos: &uint) {
        let pos = *pos;
        assert!(self.len != 0);
        if self.paged_allocs_contains_key(&pos) {
            let page_num = HeapMap::page_num(pos);
            debug!("removing %x from page map at page %x, offset %u",
                   pos, page_num, pos & PAGE_MASK);
            let mut delete_node = false;
            match self.paged_allocs.find_mut(&page_num) {
                Some(pm) => {
                    let (state, pos, len) = pm.find_alloc_pos_len(pos);
                    assert!(state == CELL_BEGIN_WHITE ||
                            state == CELL_BEGIN_BLACK);
                    pm.clear_alloc(pos, len);
                    delete_node = pm.len == 0;
                }
                None => ()
            }
            if delete_node {
                self.paged_allocs.remove(&page_num);
            }
        } else {
            debug!("removing %x from trie map", pos);
            self.extra_allocs.remove(&pos);
        }
        self.len -= 1;
    }

}


/// Helper structure stored within HeapMap and conveyed to clients
/// when inspecting and allocation records and their mark bit.
struct HeapRecord {
    size: uint,
    is_marked: bool
}


/// PageMap maps the allocations residing in a single page of the
/// heap. It is a contiguous array of words but treated logically as
/// an array of 2-bit values, each mapping a single "cell" (likely 8
/// bytes). See `BYTES_PER_CELL_LOG2` and `CellState`.
struct PageMap {
    len: uint,
    words: [uint, ..UINTS_PER_PAGE_MAP]
}

impl PageMap {

    fn new() -> PageMap {
        PageMap {
            len: 0,
            words: [0, ..UINTS_PER_PAGE_MAP ]
        }
    }

    #[inline(always)]
    fn cell_of_addr(addr: uint) -> uint {
        ((addr & PAGE_MASK) >> BYTES_PER_CELL_LOG2) as uint
    }

    #[inline(always)]
    fn cell_count_of_len(len: uint) -> uint {
        let mask = BYTES_PER_CELL - 1;
        ((len + mask) & !mask) >> BYTES_PER_CELL_LOG2
    }

    #[inline(always)]
    fn cell_word_and_bit_offset(cell: uint) -> (uint,uint) {
        let bit = cell * BITS_PER_CELL_MAP;
        (bit >> BITS_PER_WORD_LOG2, bit & WORD_MASK)
    }

    #[inline(always)]
    fn get_cell(&self, cell: uint) -> CellState {
        let (w, b) = PageMap::cell_word_and_bit_offset(cell);
        let state = ((self.words[w] >> b) & CELL_MASK) as CellState;
        // debug!("get cell %u: (word %u, bit %u) = %u", cell, w, b, state as uint);
        // debug!("word: %08x", self.words[w]);
        return state;
    }

    #[inline(always)]
    fn set_cell(&mut self, cell: uint, state: CellState) {
        let (w, b) = PageMap::cell_word_and_bit_offset(cell);
        // debug!("set cell %u: (word %u, bit %u) = %u", cell, w, b, state as uint);
        // debug!("word -: %08.8x", self.words[w]);
        self.words[w] = ((self.words[w] & !(CELL_MASK << b)) |
                         ((state as uint) << b));
        // debug!("word +: %08.8x", self.words[w]);
    }

    fn contains_alloc_starting_at_addr(&self, addr: uint) -> bool {
        let cell_num = PageMap::cell_of_addr(addr);
        let CellState = self.get_cell(cell_num);
        return CellState == CELL_BEGIN_WHITE ||
            CellState == CELL_BEGIN_BLACK;
    }

    /// Returns (CELL_EMPTY, addr, BYTES_PER_CELL) if there's no such
    /// allocation, otherwise the (CELL_BEGIN_{WHITE,BLACK}, pos, len)
    /// of the spanning allocation.

    fn find_alloc_pos_len(&self, addr: uint) -> (CellState, uint, uint) {

        let mut pos = addr;
        let mut len = 0;

        let mut lo_cell = PageMap::cell_of_addr(addr);
        let mut hi_cell = lo_cell;

        let mut lo_state = self.get_cell(lo_cell);
        let mut hi_state = lo_state;

        while lo_state == CELL_CONTD && lo_cell > 0 {
            pos -= BYTES_PER_CELL;
            len += BYTES_PER_CELL;
            lo_cell -= 1;
            lo_state = self.get_cell(lo_cell);
        }

        while hi_state == CELL_CONTD && (hi_cell+1) < CELLS_PER_PAGE {
            len += BYTES_PER_CELL;
            hi_cell += 1;
            hi_state = self.get_cell(hi_cell);
        }

        return (lo_state, pos, len);
    }

    // XXX: at the moment we only mutate marks, not length.
    // but there should not be much reason for the latter.
    fn mutate_values(&mut self, mut addr: uint,
                     f: &fn(&uint, &uint, &mut bool) -> bool) -> bool {
        let mut prev_state = CELL_EMPTY;
        let mut cell = 0;
        while cell < CELLS_PER_PAGE {
            let state = self.get_cell(cell);

            match (prev_state, state) {
                (CELL_EMPTY, CELL_BEGIN_WHITE) |
                (CELL_EMPTY, CELL_BEGIN_BLACK) => {
                    let cell_begin = cell;
                    let mut len = BYTES_PER_CELL;
                    let mut is_marked = state == CELL_BEGIN_BLACK;
                    let mark_begin = is_marked;
                    while cell+1 < CELLS_PER_PAGE && 
                        self.get_cell(cell+1) == CELL_CONTD {
                        addr += BYTES_PER_CELL;
                        len += BYTES_PER_CELL;
                        cell += 1;
                    }

                    if !f(&addr, &len, &mut is_marked) {
                        return false;
                    }

                    if is_marked != mark_begin {
                        self.set_cell(cell_begin,
                                      if is_marked {
                                          CELL_BEGIN_BLACK
                                      } else {
                                          CELL_BEGIN_WHITE
                                      });
                    }
                }
                (CELL_EMPTY, CELL_EMPTY) |
                (CELL_CONTD, CELL_EMPTY) |
                (CELL_BEGIN_BLACK, CELL_EMPTY) |
                (CELL_BEGIN_WHITE, CELL_EMPTY) => (),
                _ => {
                    fail!("unexpected cell-to-cell transition");
                }
            }
                    
            addr += BYTES_PER_CELL;
            cell += 1;
            prev_state = state;
        }
        true
    }

    #[inline(always)]
    fn set_pos_and_len(&mut self, pos: uint, len: uint,
                       first: CellState, rest: CellState) {
        let mut cell = PageMap::cell_of_addr(pos);
        let mut state = first;
        // debug!("setting pos+len for %u cells", 
        //        PageMap::cell_count_of_len(len));
        for PageMap::cell_count_of_len(len).times {
            self.set_cell(cell, state);
            cell += 1;
            state = rest;
        }
    }

    fn clear_alloc(&mut self, pos: uint, len: uint) {
        self.set_pos_and_len(pos, len, CELL_EMPTY, CELL_EMPTY);
        self.len -= 1;
    }

    fn add_alloc(&mut self, pos: uint, len: uint) {
        self.set_pos_and_len(pos, len,
                             CELL_BEGIN_WHITE,
                             CELL_CONTD);
        self.len += 1;
    }
}
