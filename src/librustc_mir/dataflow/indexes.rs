//! This submodule holds some newtype'd Index wrappers that are using
//! NonZero to ensure that Option<Index> occupies only a single word.
//! They are in a submodule to impose privacy restrictions; namely, to
//! ensure that other code does not accidentally access `index.0`
//! (which is likely to yield a subtle off-by-one error).

use std::fmt;
use core::nonzero::NonZero;
use rustc_data_structures::indexed_vec::Idx;

macro_rules! new_index {
    ($Index:ident, $debug_name:expr) => {
        #[derive(Copy, Clone, PartialEq, Eq, Hash)]
        pub struct $Index(NonZero<usize>);

        impl Idx for $Index {
            fn new(idx: usize) -> Self {
                unsafe { $Index(NonZero::new(idx + 1)) }
            }
            fn index(self) -> usize {
                *self.0 - 1
            }
        }

        impl fmt::Debug for $Index {
            fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
                write!(fmt, "{}{}", $debug_name, self.index())
            }
        }
    }
}

/// Index into MovePathData.move_paths
new_index!(MovePathIndex, "mp");

/// Index into MoveData.moves.
new_index!(MoveOutIndex, "mo");

/// Index into Borrows.locations
new_index!(BorrowIndex, "bw");
