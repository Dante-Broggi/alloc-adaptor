use std::alloc::Allocator;
use crate::QueryAlloc;

pub struct Fallback<A, B>(pub A, pub B);

unsafe impl<A: QueryAlloc, B: Allocator> Allocator for Fallback<A, B> {
    fn allocate(&self, layout: std::alloc::Layout) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        self.0.allocate(layout).or_else(|_x| {
            self.1.allocate(layout)
        })
    }

    unsafe fn deallocate(&self, ptr: std::ptr::NonNull<u8>, layout: std::alloc::Layout) {
        if self.0.owns(ptr, layout) {
            self.0.deallocate(ptr, layout);
        } else {
            self.1.deallocate(ptr, layout);
        }
    }

    fn allocate_zeroed(&self, layout: std::alloc::Layout) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        self.0.allocate_zeroed(layout).or_else(|_x| {
            self.1.allocate_zeroed(layout)
        })
    }
}

unsafe impl<A: QueryAlloc, B: QueryAlloc> QueryAlloc for Fallback<A, B> {
    unsafe fn owns(&self, ptr: std::ptr::NonNull<u8>, layout: std::alloc::Layout) -> bool {
        self.0.owns(ptr, layout) || self.1.owns(ptr, layout)
    }
}
