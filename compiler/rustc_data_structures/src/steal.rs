use std::panic::Location;

use crate::stable_hasher::{HashStable, StableHasher};
use crate::sync::{MappedReadGuard, ReadGuard, RwLock};

/// The `Steal` struct is intended to used as the value for a query.
/// Specifically, we sometimes have queries (*cough* MIR *cough*)
/// where we create a large, complex value that we want to iteratively
/// update (e.g., optimize). We could clone the value for each
/// optimization, but that'd be expensive. And yet we don't just want
/// to mutate it in place, because that would spoil the idea that
/// queries are these pure functions that produce an immutable value
/// (since if you did the query twice, you could observe the mutations).
/// So instead we have the query produce a `&'tcx Steal<mir::Body<'tcx>>`
/// (to be very specific). Now we can read from this
/// as much as we want (using `borrow()`), but you can also
/// `steal()`. Once you steal, any further attempt to read will panic.
/// Therefore, we know that -- assuming no ICE -- nobody is observing
/// the fact that the MIR was updated.
///
/// Obviously, whenever you have a query that yields a `Steal` value,
/// you must treat it with caution, and make sure that you know that
/// -- once the value is stolen -- it will never be read from again.
//
// FIXME(#41710): what is the best way to model linear queries?
#[derive(Debug)]
pub struct Steal<T> {
    value: RwLock<Option<T>>,
    prev_stolen_by: RwLock<Option<&'static Location<'static>>>,
}

impl<T> Steal<T> {
    pub fn new(value: T) -> Self {
        Steal { value: RwLock::new(Some(value)), prev_stolen_by: RwLock::new(None) }
    }

    #[track_caller]
    pub fn borrow(&self) -> MappedReadGuard<'_, T> {
        let borrow = self.value.borrow();
        if borrow.is_none() {
            panic!(
                "attempted to read from stolen value: {}, last stolen by: {}",
                std::any::type_name::<T>(),
                self.prev_stolen_by
                    .read()
                    .expect("if its stolen then prev_stolen_by should be set"),
            );
        }
        ReadGuard::map(borrow, |opt| opt.as_ref().unwrap())
    }

    #[track_caller]
    pub fn get_mut(&mut self) -> &mut T {
        self.value.get_mut().as_mut().expect("attempt to read from stolen value")
    }

    #[track_caller]
    pub fn steal(&self) -> T {
        let caller = Location::caller();
        tracing::debug!(
            "starting steal of {T} *{ADDR:x} initiated by {caller}",
            T = std::any::type_name::<T>(),
            ADDR = (self as *const _ as u64),
        );
        let value_ref = &mut *self.value.try_write().expect("stealing value which is locked");
        let value = value_ref.take();
        let mut prev_stolen_by = self.prev_stolen_by.write();
        let ret = value.unwrap_or_else(|| {
            panic!(
                "attempt to steal from stolen value, last stolen by: {}",
                prev_stolen_by.expect("if its stolen then prev_stolen_by should be set")
            );
        });
        assert_eq!(*prev_stolen_by, None);
        *prev_stolen_by = Some(caller);
        ret
    }

    /// Writers of rustc drivers often encounter stealing issues. This function makes it possible to
    /// handle these errors gracefully.
    ///
    /// This should not be used within rustc as it leaks information not tracked
    /// by the query system, breaking incremental compilation.
    #[cfg_attr(not(bootstrap), rustc_lint_untracked_query_information)]
    pub fn is_stolen(&self) -> bool {
        self.value.borrow().is_none()
    }
}

impl<CTX, T: HashStable<CTX>> HashStable<CTX> for Steal<T> {
    fn hash_stable(&self, hcx: &mut CTX, hasher: &mut StableHasher) {
        self.borrow().hash_stable(hcx, hasher);
    }
}
