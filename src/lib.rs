#![feature(allocator_api)]
#![feature(slice_ptr_len)]
#![feature(slice_ptr_get)]

use std::alloc::Allocator;
unsafe trait QueryAlloc: Allocator {
    unsafe fn owns(&self, ptr: std::ptr::NonNull<u8>, layout: std::alloc::Layout) -> bool;
}

unsafe trait AllocAll: Allocator {
    fn allocate_all(&self) -> std::ptr::NonNull<[u8]>;
}

unsafe trait DeallocAll: Allocator {
    unsafe fn deallocate_all(&self);
}

pub mod null;
pub mod fallback;
pub mod segregator;
pub mod overalloc;

#[cfg(test)]
mod tests {
    use super::*;
    use std::{alloc::{Global, Layout, System}, ptr::NonNull};


    #[test]
    #[should_panic]
    fn null_fails() {
        assert_eq!(null::Null.allocate(Layout::for_value(&0)), Err(std::alloc::AllocError));
        unsafe {
            null::Null.deallocate(NonNull::dangling(), Layout::new::<u8>());
        }
    }

    #[test]
    fn fallback_works() {
        let mut result: Vec<String, _> = Vec::new_in(fallback::Fallback(null::Null, Global));
        result.push("x".into());
        assert_eq!(result, &["x"]);
    }

    #[test]
    fn segregator_works() {
        let s = segregator::Segregator::<_, _, 4>(overalloc::Overalloc(Global), System);
        let l = Layout::from_size_align(4, 1).unwrap();
        let m = s.allocate(l).unwrap();
        assert_eq!(m.len(), 4);
        // FIXME: dealloc on assert fail, as well
        unsafe { s.deallocate(m.as_non_null_ptr(), l) };
    }

    #[test]
    fn overalloc_works() {
        let s = overalloc::Overalloc(Global);
        let b = Box::new_in(7, s);
        assert_eq!(*b, 7);
    }
}
