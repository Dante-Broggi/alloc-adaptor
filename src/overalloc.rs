use std::alloc::{Allocator, Layout};
use crate::{DeallocAll, QueryAlloc, AllocAll};

pub struct Overalloc<A>(pub A);

impl<A> Overalloc<A> {
    pub fn my_layout(layout: std::alloc::Layout) -> Result<std::alloc::Layout, std::alloc::AllocError> {
        let size = layout.size().checked_add(layout.align()).ok_or(std::alloc::AllocError)?;
        let align = layout.align().checked_add(1).map(|x| x.next_power_of_two()).ok_or(std::alloc::AllocError)?;
        Layout::from_size_align(size, align).map_err(|_| std::alloc::AllocError)
    }
}

unsafe impl<A: Allocator> Allocator for Overalloc<A> {
    fn allocate(&self, layout: std::alloc::Layout) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        self.0.allocate(Self::my_layout(layout).map_err(|_| std::alloc::AllocError)?)
    }

    unsafe fn deallocate(&self, ptr: std::ptr::NonNull<u8>, layout: std::alloc::Layout) {
        let layout = Self::my_layout(layout).unwrap();
        self.0.deallocate(ptr, layout)
    }

    fn allocate_zeroed(&self, layout: std::alloc::Layout) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        self.0.allocate_zeroed(Self::my_layout(layout).map_err(|_| std::alloc::AllocError)?)
    }

    unsafe fn grow(
        &self,
        ptr: std::ptr::NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        let old_layout = Self::my_layout(old_layout).map_err(|_| std::alloc::AllocError)?;
        let new_layout = Self::my_layout(new_layout).map_err(|_| std::alloc::AllocError)?;
        self.0.grow(ptr, old_layout, new_layout)
    }

    unsafe fn grow_zeroed(
        &self,
        ptr: std::ptr::NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        let old_layout = Self::my_layout(old_layout).map_err(|_| std::alloc::AllocError)?;
        let new_layout = Self::my_layout(new_layout).map_err(|_| std::alloc::AllocError)?;
        self.0.grow_zeroed(ptr, old_layout, new_layout)

    }

    unsafe fn shrink(
        &self,
        ptr: std::ptr::NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        let old_layout = Self::my_layout(old_layout).map_err(|_| std::alloc::AllocError)?;
        let new_layout = Self::my_layout(new_layout).map_err(|_| std::alloc::AllocError)?;
        self.0.shrink(ptr, old_layout, new_layout)

    }
}

unsafe impl<A: QueryAlloc> QueryAlloc for Overalloc<A> {
    unsafe fn owns(&self, ptr: std::ptr::NonNull<u8>, layout: std::alloc::Layout) -> bool {
        if let Ok(layout) = Self::my_layout(layout) {
            self.0.owns(ptr, layout)
        } else {
            false
        }
        
    }
}

unsafe impl<A: AllocAll> AllocAll for Overalloc<A> {
    fn allocate_all(&self) -> std::ptr::NonNull<[u8]> {
        self.0.allocate_all()
    }
}

unsafe impl<A: DeallocAll> DeallocAll for Overalloc<A> {
    unsafe fn deallocate_all(&self) {
        self.0.deallocate_all();
    }
}
