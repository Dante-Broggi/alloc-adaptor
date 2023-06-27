use std::{alloc::Allocator, ptr::NonNull, cell::Cell, ops::Deref, marker::PhantomData};
use crate::{DeallocAll, QueryAlloc};

/// a `&'static T`, except can be taken as a `*mut T`
#[repr(transparent)]
struct RawRef<T: ?Sized>(NonNull<T>, PhantomData<Cell<T>>);

impl<T: ?Sized> RawRef<T> {
    fn into_ptr(self) -> *mut T {
        self.0.as_ptr()
    }
}

impl<T: ?Sized> Clone for RawRef<T> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T: ?Sized> Copy for RawRef<T> {}

impl<T: ?Sized> Deref for RawRef<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        unsafe { self.0.as_ref() }
    }
}

/**
Store an out of line hot bitmap of used blocks
 */

pub struct BitmappedBlock<A, const BLOCK_SIZE: usize> {
    parent: A,
    blocks: usize,
    /// `Option<Box<[u64], &A>>`
    control: Cell<Option<RawRef<[Cell<u64>]>>>,
    /// `Option<Box<[Byte], &A>>`
    payload: Cell<Option<NonNull<[u8]>>>,
    start_idx: Cell<usize>,
}

impl<A, const BLOCK_SIZE: usize> BitmappedBlock<A, BLOCK_SIZE> {
    pub fn new(parent: A, blocks: usize) -> Self {
        Self { 
            parent,
            blocks,
            control: Cell::new(None),
            payload: Cell::new(None),
            start_idx: Cell::new(0),
        }
    }

    /*
    Adjusts the memoized _startIdx to the leftmost control word that has at
    least one zero bit. Assumes all control words to the left of $(D
    _control[_startIdx]) are already occupied.
    */
    fn adjust_start_idx(&self) {
        let control = self.control.get().unwrap();
        while self.start_idx.get() < control.len() 
        && control[self.start_idx.get()].get() == u64::MAX
        {
            self.start_idx.set(self.start_idx.get() + 1);
        }
    }

    /**
    Returns the blocks corresponding to the control bits starting at word index
    wordIdx and bit index msbIdx (MSB=0) for a total of howManyBlocks.
    */
    fn blocks_for(&self, word_idx: usize, msb_idx: u8, how_many_blocks: usize) -> Result<NonNull<[u8]>, std::alloc::AllocError> {
        assert!(msb_idx <= 63);
        let start = (word_idx * 64 + Into::<usize>::into(msb_idx)) * BLOCK_SIZE;
        let end = start + BLOCK_SIZE * how_many_blocks;
        let payload = self.payload.get().unwrap();
        if end <= payload.len() { 
            unsafe {
                return Ok(payload.get_unchecked_mut(start .. end)) 
            }
        };
        // This could happen if we have more control bits than available memory.
        // That's possible because the control bits are rounded up to fit in
        // 64-bit words.
        return Err(std::alloc::AllocError);
    }

    /**
    Tries to allocate "blocks" blocks at the exact position indicated by the
    position wordIdx/msbIdx (msbIdx counts from MSB, i.e. MSB has index 0). If
    it succeeds, fills "result" with the result and returns tuple(size_t.max,
    0). Otherwise, returns a tuple with the next position to search.
    */
    fn allocate_at(&self, word_idx: usize, msb_idx: u8, blocks: usize, result: &mut Result<NonNull<[u8]>, std::alloc::AllocError>) -> (usize, u8) {
        // SAFETY: we have thread local access to `self.control`
        let control = self.control.get().unwrap();
        assert!(blocks > 0);
        assert!(word_idx < control.len());
        assert!(msb_idx <= 63);
        if Into::<usize>::into(msb_idx) + blocks <= 64 {
            let blocks: u8 = blocks.try_into().unwrap();
            // Allocation should fit this control word
            if set_bits_if_zero(&control[word_idx], 64 - msb_idx - blocks, 63 - msb_idx) {
                // Success
                *result = self.blocks_for(word_idx, msb_idx, blocks.into());
                return (usize::MAX, 0);
            }
            // Can't allocate, make a suggestion
            return if msb_idx + blocks == 64
                { (word_idx + 1, 0) } else
                { (word_idx, (msb_idx + blocks)) };
        }
        // Allocation spans two control words or more
        let mask = u64::MAX >> msb_idx;
        if (control[word_idx].get() & mask) != 0 {
            // We can't allocate the rest of this control word,
            // return a suggestion.
            return (word_idx + 1, 0);
        }
        // We can allocate the rest of this control word, but we first need to
        // make sure we can allocate the tail.
        if word_idx + 1 == control.len() {
            // No more memory
            return (control.len(), 0);
        }
        let hint = self.allocate_at(word_idx + 1, 0, blocks - 64 + Into::<usize>::into(msb_idx), result);
        if hint.0 == usize::MAX {
            // We did it!
            control[word_idx].set(control[word_idx].get() | mask);
            *result = self.blocks_for(word_idx, msb_idx, blocks);
            return (usize::MAX, 0);
        }
        // Failed, return a suggestion that skips this whole run.
        return hint;
    }

    /** Allocates as many blocks as possible at the end of the blocks indicated
    by wordIdx. Returns the number of blocks allocated. */
    fn allocate_at_tail(&self, word_idx: usize) -> u32 {
        let control = self.control.get().unwrap();
        assert!(word_idx < control.len());
        let available = (control[word_idx].get()).trailing_zeros();
        control[word_idx].set(control[word_idx].get() | u64::MAX >> available);
        return available;
    }

    fn small_alloc(&self, blocks: u8) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        assert!(blocks >= 2 && blocks <= 64);
        let control = self.control.get().unwrap();
        for i in self.start_idx.get() .. control.len() {
            // Test within the current 64-bit word
            let v = control[i].get();
            if v == u64::MAX { continue };
            let j = find_contig_ones(!v, blocks);
            if j < 64 {
                let j = j.try_into().unwrap();
                // yay, found stuff
                set_bits(&control[i], 64 - j - blocks, 63 - j);
                return self.blocks_for(i, j, blocks.into());
            }
            // Next, try allocations that cross a word
            let available: u8 = v.trailing_zeros().try_into().unwrap();
            if available == 0 { continue };
            if i + 1 >= control.len() { break };
            assert!(available < blocks.into()); // otherwise we should have found it
            let needed = blocks - available;
            assert!(needed > 0 && needed < 64);
            if self.allocate_at_front(i + 1, needed) {
                // yay, found a block crossing two words
                control[i].set(control[i].get() | (1_u64 << available) - 1);
                return self.blocks_for(i, 64 - available, blocks.into());
            }
        }
        return Err(std::alloc::AllocError);
    }

    fn huge_alloc(&self, blocks: usize) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        assert!(blocks > 64);
        let mut result = Err(std::alloc::AllocError);
        let mut pos = (self.start_idx.get(), 0);
        let control = self.control.get().unwrap();
        loop {
            if pos.0 >= control.len() {
                // No more memory
                return Err(std::alloc::AllocError);
            }
            pos = self.allocate_at(pos.0, pos.1, blocks, &mut result);
            if pos.0 == usize::MAX {
                // Found and allocated
                return result;
            }
        }
    }

    /// Rounds sizeInBytes to a multiple of blockSize.
    fn bytes2blocks(size_in_bytes: usize) -> usize {
        (size_in_bytes + BLOCK_SIZE - 1) / BLOCK_SIZE
    }

    /** Allocates given blocks at the beginning blocks indicated by wordIdx.
    Returns true if allocation was possible, false otherwise. */
    fn allocate_at_front(&self, word_idx: usize, blocks: u8) -> bool {
        let control = self.control.get().unwrap();
        assert!(word_idx < control.len() && blocks >= 1 && blocks <= 64);
        let mask = (1 << (64 - blocks)) - 1;
        if control[word_idx].get() > mask { return false };
        // yay, works
        control[word_idx].set(control[word_idx].get() | !mask);
        return true;
    } 
}

unsafe impl<A: Allocator, const BLOCK_SIZE: usize> Allocator for BitmappedBlock<A, BLOCK_SIZE> {
    fn allocate(&self, layout: std::alloc::Layout) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        if layout.align() != 1 {
            // FIXME: handle aligned alloc requests
            return Err(std::alloc::AllocError);
        }
        if self.control.get().is_none() {
            // Lazy initialize
        }
        assert!((self.blocks != 0) && self.control.get().is_some() && self.payload.get().is_some());
        let control = self.control.get().unwrap();
        let blocks = Self::bytes2blocks(layout.size());
        
        match blocks {
            1 => {
                // inline code here for speed
                // find the next available block
                for i in self.start_idx.get() .. control.len() {
                    let w = control[i].get();
                    if w == u64::MAX { continue };
                    let j: u8 = w.leading_ones().try_into().unwrap();
                    assert!(j < 64);
                    assert!((control[i].get() & ((1_u64 << 63) >> j)) == 0);
                    control[i].set(control[i].get() | (1_u64 << 63) >> j);
                    if i == self.start_idx.get() {
                        self.adjust_start_idx();
                    }
                    return self.blocks_for(i, j, 1);
                }
                Err(std::alloc::AllocError)
            },
            0 => {
                Err(std::alloc::AllocError)
            },
            2..=63 => {
                self.small_alloc(blocks.try_into().unwrap())
            },
            _ => {
                self.huge_alloc(blocks)
            }
        }
    }

    unsafe fn deallocate(&self, ptr: std::ptr::NonNull<u8>, layout: std::alloc::Layout) {
        // Round up size to multiple of block size
        let mut blocks: usize = Self::bytes2blocks(layout.size());
        // Locate position
        let pos = ptr.as_ptr().sub_ptr(self.payload.get().unwrap().as_mut_ptr());
        assert_eq!(pos % BLOCK_SIZE, 0);
        let block_idx = pos / BLOCK_SIZE;
        let mut word_idx = block_idx / 64;
        let mut msb_idx: u8 = (block_idx % 64).try_into().unwrap();
        if self.start_idx.get() > word_idx { self.start_idx.set(word_idx) };

        let control = self.control.get().unwrap();
        
        // Three stages: heading bits, full words, leftover bits
        if msb_idx != 0 {
            if blocks + Into::<usize>::into(msb_idx) <= 64 {
                let blocks: u8 = blocks.try_into().unwrap();
                reset_bits(&control[word_idx], 64 - msb_idx - blocks, 63 - msb_idx);
                return;
            } else {
                control[word_idx].set(control[word_idx].get() & u64::MAX << 64 - msb_idx);
                blocks -= 64_usize - Into::<usize>::into(msb_idx);
                word_idx += 1;
                msb_idx = 0;
            }
        }
        
        // Stage 2: reset one word at a time
        while blocks >= 64 {
            control[word_idx].set(0);
            word_idx += 1;
            blocks -= 64;
        }
        
        // Stage 3: deal with leftover bits, if any
        assert!(word_idx <= control.len());
        if blocks != 0 {
            control[word_idx].set(control[word_idx].get() & u64::MAX >> blocks);
        }
    }
}

unsafe impl<A: Allocator, const N: usize> QueryAlloc for BitmappedBlock<A, N> {
    unsafe fn owns(&self, ptr: std::ptr::NonNull<u8>, layout: std::alloc::Layout) -> bool {
        self.payload.get().is_some_and(|p| {
            ptr.as_ptr() >= p.as_mut_ptr()
            && ptr.addr().get() + layout.size() <= p.as_mut_ptr().addr() + p.len()
        })
    }
}

unsafe impl<A: Allocator, const N: usize> DeallocAll for BitmappedBlock<A, N> {
    unsafe fn deallocate_all(&self) {
        self.control.replace(None).map(|x| Box::from_raw_in(x.into_ptr(), self.parent.by_ref()));
        self.payload.replace(None).map(|x| Box::from_raw_in(x.as_ptr(), self.parent.by_ref()));
        self.start_idx.set(0);
    }
}

/**
Finds a run of contiguous ones in $(D x) of length at least $(D n).

```
    use alloc_adaptor::bitmap::findContigOnes;
    assert_eq!(findContigOnes(0x0000_0000_0000_0300, 2), 54);
    assert_eq!(findContigOnes(!0_u64, 1), 0);
    assert_eq!(findContigOnes(!0_u64, 2), 0);
    assert_eq!(findContigOnes(!0_u64, 32), 0);
    assert_eq!(findContigOnes(!0_u64, 64), 0);
    assert_eq!(findContigOnes(0_u64, 1), 64);
    assert_eq!(findContigOnes(0x4000_0000_0000_0000, 1), 1);
    assert_eq!(findContigOnes(0x0000_0F00_0000_0000, 4), 20);
```

*/
pub fn find_contig_ones(mut x: u64, mut n: u8) -> u32 {
    while n > 1 {
        let s = n >> 1;
        x &= x << s;
        n -= s;
    }
    (!x).leading_ones()
}

/**
```
    assert_eq!(0_u64.trailing_zeros(), 64);
    assert_eq!(1_u64.trailing_zeros(), 0);
    assert_eq!(2_u64.trailing_zeros(), 1);
    assert_eq!(3_u64.trailing_zeros(), 0);
    assert_eq!(4_u64.trailing_zeros(), 2);
 ```
 */
const _: () = ();

/**
Unconditionally sets the bits from lsb through msb in w to zero.

```
    use alloc_adaptor::bitmap::set_bits;
    let mut w: u64;
    w = 0; set_bits(&mut w, 0, 63); assert_eq!(w, u64::MAX);
    w = 0; set_bits(&mut w, 1, 63); assert_eq!(w, u64::MAX - 1);
    w = 6; set_bits(&mut w, 0, 1); assert_eq!(w, 7);
    w = 6; set_bits(&mut w, 3, 3); assert_eq!(w, 14);
```

*/
pub fn set_bits(w: &Cell<u64>, lsb: u8, msb: u8) {
    assert!(lsb <= msb && msb < 64);
    let mask = (u64::MAX << lsb) & (u64::MAX >> (63 - msb));
    w.set(w.get() | mask);
}

/** Are bits from lsb through msb in w zero? If so, make then 1
and return the resulting w. Otherwise, just return 0.
*/
fn set_bits_if_zero(w: &Cell<u64>, lsb: u8, msb: u8) -> bool {
    assert!(lsb <= msb && msb < 64);
    let mask = (u64::MAX << lsb) & (u64::MAX >> (63 - msb));
    if (w.get() & mask) != 0 { return false };
    w.set(w.get() | mask);
    return true;
}

/// Assigns bits in w from lsb through msb to zero.
fn reset_bits(w: &Cell<u64>, lsb: u8, msb: u8) {
    assert!(lsb <= msb && msb < 64);
    let mask = (u64::MAX << lsb) & (u64::MAX >> (63 - msb));
    w.set(w.get() & !mask);
}
