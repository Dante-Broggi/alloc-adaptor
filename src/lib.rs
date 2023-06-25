#![feature(allocator_api)]

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

#[cfg(test)]
mod tests {
    use super::*;
    use std::alloc::Global;

    #[test]
    fn fallback_works() {
        let mut result: Vec<String, _> = Vec::new_in(fallback::Fallback(null::Null, Global));
        result.push("x".into());
        assert_eq!(result, &["x"]);
    }
}
