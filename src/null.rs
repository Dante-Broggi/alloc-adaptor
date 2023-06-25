use std::{alloc::Allocator, ptr::NonNull};
use crate::{AllocAll, DeallocAll, QueryAlloc};

pub struct Null;

unsafe impl Allocator for Null {
    fn allocate(&self, _layout: std::alloc::Layout) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        Err(std::alloc::AllocError)
    }

    unsafe fn deallocate(&self, _ptr: std::ptr::NonNull<u8>, _layout: std::alloc::Layout) {
        panic!()
    }

    fn allocate_zeroed(&self, _layout: std::alloc::Layout) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        Err(std::alloc::AllocError)
    }

    unsafe fn grow(
        &self,
        _ptr: std::ptr::NonNull<u8>,
        _old_layout: std::alloc::Layout,
        _new_layout: std::alloc::Layout,
    ) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        // we cannot get here as no pointers are ever "currently allocated"
        panic!()
        // the effective default impl
        // Err(std::alloc::AllocError)
    }

    unsafe fn grow_zeroed(
        &self,
        _ptr: std::ptr::NonNull<u8>,
        _old_layout: std::alloc::Layout,
        _new_layout: std::alloc::Layout,
    ) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        // we cannot get here as no pointers are ever "currently allocated"
        panic!()
        // the effective default impl
        // Err(std::alloc::AllocError)
    }

    unsafe fn shrink(
        &self,
        _ptr: std::ptr::NonNull<u8>,
        _old_layout: std::alloc::Layout,
        _new_layout: std::alloc::Layout,
    ) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        // we cannot get here as no pointers are ever "currently allocated"
        panic!()
        // the effective default impl
        // Err(std::alloc::AllocError)
    }

    fn by_ref(&self) -> &Self
    where
        Self: Sized,
    {
        self
    }
}

unsafe impl QueryAlloc for Null {
    unsafe fn owns(&self, _ptr: std::ptr::NonNull<u8>, _layout: std::alloc::Layout) -> bool {
        false
    }
}

// unsafe impl AllocAll for Null {
//     fn allocate_all(&self) -> std::ptr::NonNull<[u8]> {
//        // would require allowing zero deallocate.
//        unsafe { NonNull::new_unchecked(core::ptr::slice_from_raw_parts_mut(self as *const _ as *mut u8, 0)) }
//     }
// }

unsafe impl DeallocAll for Null {
    unsafe fn deallocate_all(&self) {}
}
