use core::kinds::marker;

/// `DstSlice<T>` is a placeholder for the unimplemented (i.e. current non-type) `[T]`.
pub struct DstSlice<T> {
    marker: marker::InvariantType<T>,
}

pub struct PointerExtra<type U> {
    opaque: uint,
    marker: marker::InvariantType<U>,
}

fn wrap_extra<type T>(opaque: uint) -> PointerExtra<T> {
    PointerExtra { marker: marker::InvariantType, opaque: opaque }
}

#[allow(dead_code)]
fn thin_pointer_data<T>() -> PointerExtra<T> {
    wrap_extra(0)
}

#[allow(dead_code)]
fn array_pointer_data<T>(length: uint) -> PointerExtra<DstSlice<T>> {
    wrap_extra(length)
}

#[cfg(not(stage0))]
extern "rust-intrinsic" {
    fn dst_pointer_extra_data<type U1, type U2>(x: *U1) -> uint;
    fn dst_pointer_mem<type U>(x: *U) -> *mut u8;
    fn dst_make_pointer<type U>(p: *mut u8, data: uint) -> *mut U;

    fn dst_sizeof_type<type U>(data: uint) -> uint;
    fn dst_alignof_type<type U>(data: uint) -> uint;
}

#[cfg(stage0)]
fn dst_pointer_extra_data<type U1, type U2>(_x: *U1) -> uint { fail!("not yet implemented") }
#[cfg(stage0)]
fn dst_pointer_mem<type U>(_x: *U) -> *mut u8 { fail!("not yet implemented") }
#[cfg(stage0)]
fn dst_make_pointer<type U>(_p: *mut u8, _data: uint) -> *mut U { fail!("not yet implemented") }
#[cfg(stage0)]
fn dst_sizeof_type<type U>(_data: uint) -> uint { fail!("not yet implemented") }
#[cfg(stage0)]
fn dst_alignof_type<type U>(_data: uint) -> uint { fail!("not yet implemented") }

pub fn pointer_data<type U1, type U2>(x: &U1) -> PointerExtra<U2> {
    // use core::intrinsics::dst_pointer_extra_data;
    wrap_extra(dst_pointer_extra_data::<U1,U2>(x as *U1))
}
pub fn pointer_mem<type U>(x: &U) -> *mut u8 {
    // use core::intrinsics::dst_pointer_mem;
    dst_pointer_mem(x as *U)
}
pub fn make_pointer<type U>(p: *mut u8, data: PointerExtra<U>) -> *mut U {
    dst_make_pointer(p, data.opaque)
}
pub fn sizeof_type<type U>(data: PointerExtra<U>) -> uint {
    dst_sizeof_type::<U>(data.opaque)
}
pub fn alignof_type<type U>(data: PointerExtra<U>) -> uint {
    dst_alignof_type::<U>(data.opaque)
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
