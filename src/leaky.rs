use std::alloc::Allocator;
use crate::{DeallocAll, QueryAlloc, AllocAll};

/// Behaves like the inner allocator for allocation and reallocation functions,
/// but does nothing for deallocation functions.
pub struct Leaky<A>(pub A);

unsafe impl<A: Allocator> Allocator for Leaky<A> {
    fn allocate(&self, layout: std::alloc::Layout) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        self.0.allocate(layout)
    }

    unsafe fn deallocate(&self, _ptr: std::ptr::NonNull<u8>, _layout: std::alloc::Layout) {
        // nada
    }

    fn allocate_zeroed(&self, layout: std::alloc::Layout) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        self.0.allocate_zeroed(layout)
    }

    unsafe fn grow(
        &self,
        ptr: std::ptr::NonNull<u8>,
        old_layout: std::alloc::Layout,
        new_layout: std::alloc::Layout,
    ) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        self.0.grow(ptr, old_layout, new_layout)
    }

    unsafe fn grow_zeroed(
        &self,
        ptr: std::ptr::NonNull<u8>,
        old_layout: std::alloc::Layout,
        new_layout: std::alloc::Layout,
    ) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        self.0.grow_zeroed(ptr, old_layout, new_layout)
    }

    unsafe fn shrink(
        &self,
        ptr: std::ptr::NonNull<u8>,
        old_layout: std::alloc::Layout,
        new_layout: std::alloc::Layout,
    ) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        self.0.shrink(ptr, old_layout, new_layout)
    }
}

unsafe impl<A: QueryAlloc> QueryAlloc for Leaky<A> {
    unsafe fn owns(&self, ptr: std::ptr::NonNull<u8>, layout: std::alloc::Layout) -> bool {
        self.0.owns(ptr, layout)
    }
}

unsafe impl<A: AllocAll> AllocAll for Leaky<A> {
    fn allocate_all(&self) -> std::ptr::NonNull<[u8]> {
        self.0.allocate_all()
    }
    fn allocate_all_zeroed(&self) -> std::ptr::NonNull<[u8]> {
        self.0.allocate_all_zeroed()
    }
}

unsafe impl<A: Allocator> DeallocAll for Leaky<A> {
    unsafe fn deallocate_all(&self) {
        // nada
    }
}
