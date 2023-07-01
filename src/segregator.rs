use std::{alloc::Allocator, ptr::NonNull};
use crate::{DeallocAll, QueryAlloc};

pub struct Segregator<Small, Large, const N: usize>(pub Small, pub Large);

unsafe impl<Small: Allocator, Large: Allocator, const N: usize> Allocator for Segregator<Small, Large, N> {
    fn allocate(&self, layout: std::alloc::Layout) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        if layout.size() <= N {
            // We cannot allow large allocations from `Small` to escape
            // as we would deallocate them with `Large`
            let ptr = self.0.allocate(layout)?.as_ptr();
            let len = core::cmp::min(ptr.len(), N);
            let ptr = core::ptr::slice_from_raw_parts_mut(ptr.as_mut_ptr(), len);
            Ok(NonNull::new(ptr).unwrap())
        } else {
            self.1.allocate(layout)
        }
    }

    unsafe fn deallocate(&self, ptr: std::ptr::NonNull<u8>, layout: std::alloc::Layout) {
        if layout.size() <= N {
            self.0.deallocate(ptr, layout);
        } else {
            self.1.deallocate(ptr, layout);
        }
    }

    fn allocate_zeroed(&self, layout: std::alloc::Layout) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        if layout.size() <= N {
            // We cannot allow large allocations from `Small` to escape
            // as we would deallocate them with `Large`
            let ptr = self.0.allocate_zeroed(layout)?.as_ptr();
            let len = core::cmp::min(ptr.len(), N);
            let ptr = core::ptr::slice_from_raw_parts_mut(ptr.as_mut_ptr(), len);
            Ok(NonNull::new(ptr).unwrap())
        } else {
            self.1.allocate_zeroed(layout)
        }
    }
}

unsafe impl<Small: QueryAlloc, B: QueryAlloc, const N: usize> QueryAlloc for Segregator<Small, B, N> {
    unsafe fn owns(&self, ptr: std::ptr::NonNull<u8>, layout: std::alloc::Layout) -> bool {
        if layout.size() <= N {
            self.0.owns(ptr, layout)
        } else {
            self.1.owns(ptr, layout)
        }
    }
}

// Not provided because we cannot gauruntee we are the only access to self.{0,1}
// unsafe impl<Small: DeallocAll, B: DeallocAll, const N: usize> DeallocAll for Segregator<Small, B, N> {
//     unsafe fn deallocate_all(&self) {
//         self.0.deallocate_all();
//         self.1.deallocate_all();
//     }
// }
