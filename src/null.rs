use std::alloc::Allocator;
use crate::QueryAlloc;

pub struct Null;

unsafe impl Allocator for Null {
    fn allocate(&self, layout: std::alloc::Layout) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        Err(std::alloc::AllocError)
    }

    unsafe fn deallocate(&self, ptr: std::ptr::NonNull<u8>, layout: std::alloc::Layout) {
        panic!()
    }
}

unsafe impl QueryAlloc for Null {
    unsafe fn owns(&self, _ptr: std::ptr::NonNull<u8>, _layout: std::alloc::Layout) -> bool {
        false
    }
}
