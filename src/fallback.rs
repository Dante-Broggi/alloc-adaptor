use std::alloc::Allocator;
use crate::{DeallocAll, QueryAlloc};

/**
`Fallback` is the allocator equivalent of an "or" operator in
algebra. An allocation request is first attempted with `A`. 
If that fails, the request is forwarded to `B`. 
All other requests are dispatched appropriately to one of
the two allocators.

In order to work, `Fallback` requires that `A` implement `QueryAlloc`. 
This is needed in order to decide which allocator was
responsible for a given allocation.

$(D FallbackAllocator) is useful for fast, special-purpose allocators backed up
by general-purpose allocators.
*/
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

    unsafe fn grow(
        &self,
        ptr: std::ptr::NonNull<u8>,
        old_layout: std::alloc::Layout,
        new_layout: std::alloc::Layout,
    ) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        debug_assert!(
            new_layout.size() >= old_layout.size(),
            "`new_layout.size()` must be greater than or equal to `old_layout.size()`"
        );
        let local = if self.0.owns(ptr, old_layout) {
            self.0.grow(ptr, old_layout, new_layout)
        } else {
            self.1.grow(ptr, old_layout, new_layout)
        };
        match local {
            Ok(x) => { Ok(x) },
            Err(_) => {
                let new_ptr = self.allocate(new_layout)?;

                // SAFETY: because `new_layout.size()` must be greater than or equal to
                // `old_layout.size()`, both the old and new memory allocation are valid for reads and
                // writes for `old_layout.size()` bytes. Also, because the old allocation wasn't yet
                // deallocated, it cannot overlap `new_ptr`. Thus, the call to `copy_nonoverlapping` is
                // safe. The safety contract for `dealloc` must be upheld by the caller.
                unsafe {
                    std::ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_mut_ptr(), old_layout.size());
                    self.deallocate(ptr, old_layout);
                }

                Ok(new_ptr)
            }
        }
    }

    unsafe fn grow_zeroed(
        &self,
        ptr: std::ptr::NonNull<u8>,
        old_layout: std::alloc::Layout,
        new_layout: std::alloc::Layout,
    ) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        debug_assert!(
            new_layout.size() >= old_layout.size(),
            "`new_layout.size()` must be greater than or equal to `old_layout.size()`"
        );
        let local = if self.0.owns(ptr, old_layout) {
            self.0.grow_zeroed(ptr, old_layout, new_layout)
        } else {
            self.1.grow_zeroed(ptr, old_layout, new_layout)
        };
        match local {
            Ok(x) => { Ok(x) },
            Err(_) => {
                let new_ptr = self.allocate_zeroed(new_layout)?;

                // SAFETY: because `new_layout.size()` must be greater than or equal to
                // `old_layout.size()`, both the old and new memory allocation are valid for reads and
                // writes for `old_layout.size()` bytes. Also, because the old allocation wasn't yet
                // deallocated, it cannot overlap `new_ptr`. Thus, the call to `copy_nonoverlapping` is
                // safe. The safety contract for `dealloc` must be upheld by the caller.
                unsafe {
                    std::ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_mut_ptr(), old_layout.size());
                    self.deallocate(ptr, old_layout);
                }

                Ok(new_ptr)
            }
        }
    }

    unsafe fn shrink(
        &self,
        ptr: std::ptr::NonNull<u8>,
        old_layout: std::alloc::Layout,
        new_layout: std::alloc::Layout,
    ) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        debug_assert!(
            new_layout.size() <= old_layout.size(),
            "`new_layout.size()` must be smaller than or equal to `old_layout.size()`"
        );
        let local = if self.0.owns(ptr, old_layout) {
            self.0.shrink(ptr, old_layout, new_layout)
        } else {
            self.1.shrink(ptr, old_layout, new_layout)
        };
        match local {
            Ok(x) => { Ok(x) },
            Err(_) => {
                let new_ptr = self.allocate(new_layout)?;

                // SAFETY: because `new_layout.size()` must be lower than or equal to
                // `old_layout.size()`, both the old and new memory allocation are valid for reads and
                // writes for `new_layout.size()` bytes. Also, because the old allocation wasn't yet
                // deallocated, it cannot overlap `new_ptr`. Thus, the call to `copy_nonoverlapping` is
                // safe. The safety contract for `dealloc` must be upheld by the caller.
                unsafe {
                    std::ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_mut_ptr(), new_layout.size());
                    self.deallocate(ptr, old_layout);
                }
        
                Ok(new_ptr)
            },
        }
    }
}

unsafe impl<A: QueryAlloc, B: QueryAlloc> QueryAlloc for Fallback<A, B> {
    unsafe fn owns(&self, ptr: std::ptr::NonNull<u8>, layout: std::alloc::Layout) -> bool {
        self.0.owns(ptr, layout) || self.1.owns(ptr, layout)
    }
}

// Not provided because we cannot gauruntee we are the only access to self.{0,1}
// unsafe impl<A: DeallocAll + QueryAlloc, B: DeallocAll> DeallocAll for Fallback<A, B> {
//     unsafe fn deallocate_all(&self) {
//         self.0.deallocate_all();
//         self.1.deallocate_all();
//     }
// }
