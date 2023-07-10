use std::alloc::Allocator;
use crate::{DeallocAll, QueryAlloc, AllocAll};

/// Behaves like the inner allocator, but allways uses the `*_zeroed` versions of the functions if available.
pub struct Zeroed<A>(pub A);

unsafe impl<A: Allocator> Allocator for Zeroed<A> {
    fn allocate(&self, layout: std::alloc::Layout) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        self.0.allocate_zeroed(layout)
    }

    unsafe fn deallocate(&self, ptr: std::ptr::NonNull<u8>, layout: std::alloc::Layout) {
        self.0.deallocate(ptr, layout)
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
        self.0.grow_zeroed(ptr, old_layout, new_layout)
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

unsafe impl<A: QueryAlloc> QueryAlloc for Zeroed<A> {
    unsafe fn owns(&self, ptr: std::ptr::NonNull<u8>, layout: std::alloc::Layout) -> bool {
        self.0.owns(ptr, layout)
    }
}

unsafe impl<A: AllocAll> AllocAll for Zeroed<A> {
    fn allocate_all(&self) -> std::ptr::NonNull<[u8]> {
        self.0.allocate_all_zeroed()
    }
    fn allocate_all_zeroed(&self) -> std::ptr::NonNull<[u8]> {
        self.0.allocate_all_zeroed()
    }
}

// Not provided because we cannot gauruntee we are the only access to self.0
// unsafe impl<A: DeallocAll> DeallocAll for Zeroed<A> {
//     unsafe fn deallocate_all(&self) {
//         self.0.deallocate_all()
//     }
// }
