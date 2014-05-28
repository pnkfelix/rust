use core::kinds::marker::InvariantType;

/// DstSlice<T> is a placeholder for the current non-type [T].
pub struct DstSlice<T>;

pub struct PointerExtra<type U> {
    opaque: uint,
    marker: InvariantType<U>,
}

/// FIXME: document Allocator protocol.  Try to keep it in sync with
/// my draft of the Allocator RFC.
#[lang="allocator"]
pub trait Alloc<type U> {
    fn malloc(&self, extra: PointerExtra<U>) -> *U;
    fn free(&self, pointer: *U);
}

#[cfg(not(has_defaults))]
#[lang="array_allocator"]
pub trait AllocVec<T> : Alloc<DstSlice<T>> {
    fn malloc_array(&self, capacity: uint) -> *mut T;

    fn realloc_array(&self,
                     old_pointer: *mut T,
                     old_capacity: uint, new_capacity: uint) -> *mut T;

    fn free_array(&self,
                  pointer: *mut T,
                  capacity: uint);

    fn shrink_to_fit(&self,
                     pointer: *T,
                     old_capacity: uint,
                     initialized_length: uint) -> *DstSlice<T>;
}

#[cfg(has_defaults)]
#[lang="array_allocator"]
pub trait AllocVec<T> : Alloc<[T]> {
    fn malloc_array(&self, capacity: uint) -> *mut T {
        let data = array_pointer_data(capacity);
        transmute::<*mut u8, *mut T>(pointer_mem(self.malloc(data)))
    }

    fn realloc_array(&self,
                     old_pointer: *mut T,
                     old_capacity: uint, new_capacity: uint) -> *mut T {
        let new_pointer = self.malloc_array(new_capacity);
        copy(new_pointer, old_pointer, min(old_capacity, new_capacity));
        self.free_array(old_pointer, old_capacity);
        new_pointer
    }

    fn free_array(&self,
                  pointer: *mut T,
                  capacity: uint) {
        let data: PointerExtra<[T]> = array_pointer_data(capacity);
        self.free(make_pointer(pointer, data))
    }

    fn shrink_to_fit(&self,
                     pointer: *T,
                     old_capacity: uint,
                     initialized_length: uint) -> *[T] {
        let p = self.realloc_array(pointer, old_capacity, initialized_length);
        let data: PointerExtra<[T]> = array_pointer_data(initialized_length);
        make_pointer(p, data)
    }
}
