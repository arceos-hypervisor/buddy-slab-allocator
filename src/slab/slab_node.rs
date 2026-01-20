//! Slab node implementation.
//!
//! This module defines the SlabNode structure which manages exactly 512 objects
//! using a fixed bitmap.

#[cfg(feature = "log")]
use log::error;

pub use super::slab_byte_allocator::SizeClass;

#[repr(C)]
pub(crate) struct SlabHeader {
    magic: u32,
    size_class: u16,
    object_count: u16,
    free_count: u16,
    _reserved: u16,
    slab_bytes: usize,
    prev: usize,
    next: usize,
    free_bitmap: [u64; FREE_BITMAP_WORDS],
}

const SLAB_HEADER_MAGIC: u32 = 0x534c_4142;
const FREE_BITMAP_WORDS: usize = 8;

#[derive(Debug, Clone, Copy)]
pub struct SlabNode {
    pub addr: usize,           // Starting physical address
    pub size_class: SizeClass, // Size class
}

impl SlabNode {
    pub const MAX_OBJECTS: usize = FREE_BITMAP_WORDS * 64;

    pub const fn new(addr: usize, size_class: SizeClass) -> Self {
        Self { addr, size_class }
    }

    fn header_size_aligned(&self) -> usize {
        crate::align_up(core::mem::size_of::<SlabHeader>(), self.size_class.size())
    }

    fn object_base(&self) -> usize {
        self.addr + self.header_size_aligned()
    }

    fn header(&self) -> &SlabHeader {
        unsafe { &*(self.addr as *const SlabHeader) }
    }

    fn header_mut(&mut self) -> &mut SlabHeader {
        unsafe { &mut *(self.addr as *mut SlabHeader) }
    }

    pub fn init_header(&mut self, slab_bytes: usize) {
        let object_size = self.size_class.size();
        let header_size_aligned = self.header_size_aligned();
        let object_count = if slab_bytes > header_size_aligned {
            (slab_bytes - header_size_aligned) / object_size
        } else {
            0
        }
        .min(Self::MAX_OBJECTS);

        if object_count == 0 {
            return;
        }

        let mut free_bitmap = [u64::MAX; FREE_BITMAP_WORDS];
        if object_count < Self::MAX_OBJECTS {
            let full_words = object_count / 64;
            let rem_bits = object_count % 64;
            for i in 0..FREE_BITMAP_WORDS {
                if i < full_words {
                    continue;
                }
                if i == full_words {
                    if rem_bits == 0 {
                        free_bitmap[i] = 0;
                    } else {
                        free_bitmap[i] &= (1u64 << rem_bits) - 1;
                    }
                } else {
                    free_bitmap[i] = 0;
                }
            }
        }

        let header = self.header_mut();
        *header = SlabHeader {
            magic: SLAB_HEADER_MAGIC,
            size_class: object_size as u16,
            object_count: object_count as u16,
            free_count: object_count as u16,
            _reserved: 0,
            slab_bytes,
            prev: 0,
            next: 0,
            free_bitmap,
        };
    }

    pub fn is_valid_for_size_class(&self) -> bool {
        let header = self.header();
        header.magic == SLAB_HEADER_MAGIC && header.size_class as usize == self.size_class.size()
    }

    pub fn in_use(&self) -> u32 {
        let header = self.header();
        header.object_count as u32 - header.free_count as u32
    }

    pub fn free_count(&self) -> u32 {
        self.header().free_count as u32
    }

    pub fn is_full(&self) -> bool {
        self.header().free_count == 0
    }

    pub fn is_empty(&self) -> bool {
        self.header().free_count == self.header().object_count
    }

    pub fn alloc_object(&mut self) -> Option<usize> {
        let header = self.header_mut();
        if header.free_count == 0 {
            return None;
        }
        let object_count = header.object_count as usize;
        for (word_idx, &word) in header.free_bitmap.iter().enumerate() {
            if word != 0 {
                let bit_pos = word.trailing_zeros() as usize;
                let object_index = word_idx * 64 + bit_pos;

                if object_index >= object_count {
                    continue;
                }

                header.free_bitmap[word_idx] &= !(1u64 << bit_pos);
                header.free_count -= 1;
                return Some(object_index);
            }
        }
        None
    }

    pub fn dealloc_object(&mut self, object_index: usize) -> bool {
        let header = self.header_mut();
        if object_index < header.object_count as usize {
            let word_idx = object_index / 64;
            let bit_idx = object_index % 64;
            let mask = 1u64 << bit_idx;
            let was_free = (header.free_bitmap[word_idx] & mask) != 0;

            if was_free {
                // Object is already free (double-free), return false to indicate no actual change
                return false;
            }

            header.free_bitmap[word_idx] |= mask;
            header.free_count = header.free_count.saturating_add(1);
            true // Object was successfully deallocated
        } else {
            false
        }
    }

    pub fn object_addr(&self, object_index: usize) -> usize {
        self.object_base() + object_index * self.size_class.size()
    }

    pub fn object_index_from_addr(&self, obj_addr: usize) -> Option<usize> {
        let base = self.object_base();
        if obj_addr < base {
            return None;
        }

        let offset = obj_addr - base;
        if offset % self.size_class.size() != 0 {
            error!("Invalid object address: {:x}", obj_addr);
            return None;
        }

        let object_index = offset / self.size_class.size();

        if object_index < self.header().object_count as usize {
            Some(object_index)
        } else {
            None
        }
    }

    pub fn page_count(&self, page_size: usize) -> usize {
        let object_size = self.size_class.size();
        let bytes_needed = Self::MAX_OBJECTS * object_size;
        (bytes_needed + page_size - 1) / page_size
    }

    pub fn prev(&self) -> Option<usize> {
        let prev = self.header().prev;
        if prev == 0 {
            None
        } else {
            Some(prev)
        }
    }

    pub fn next(&self) -> Option<usize> {
        let next = self.header().next;
        if next == 0 {
            None
        } else {
            Some(next)
        }
    }

    pub fn set_prev(&mut self, prev: Option<usize>) {
        self.header_mut().prev = prev.unwrap_or(0);
    }

    pub fn set_next(&mut self, next: Option<usize>) {
        self.header_mut().next = next.unwrap_or(0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::alloc::{alloc, dealloc};
    use core::alloc::Layout;

    #[test]
    fn test_slab_node() {
        let mut node = SlabNode::new(0, SizeClass::Bytes64);
        let slab_pages = node.page_count(4096);
        let slab_bytes = slab_pages * 4096;
        let layout = Layout::from_size_align(slab_bytes, slab_bytes).unwrap();
        let base = unsafe { alloc(layout) } as usize;
        assert_ne!(base, 0);
        node.addr = base;
        node.init_header(slab_bytes);

        assert!(node.is_empty());
        assert!(!node.is_full());
        assert!(node.free_count() <= SlabNode::MAX_OBJECTS as u32);
        assert_eq!(node.in_use(), 0);

        // Test allocation
        let obj_idx = node.alloc_object().unwrap();
        assert_eq!(node.object_addr(obj_idx), node.object_base());
        assert_eq!(node.in_use(), 1);
        assert_eq!(
            node.free_count(),
            (node.header().object_count as u32).saturating_sub(1)
        );

        // Test deallocation
        node.dealloc_object(obj_idx);
        assert!(node.is_empty());
        assert_eq!(node.in_use(), 0);
        assert_eq!(node.free_count(), node.header().object_count as u32);

        unsafe { dealloc(base as *mut u8, layout) };
    }

    #[test]
    fn test_object_index_from_addr() {
        let mut node = SlabNode::new(0, SizeClass::Bytes64);
        let slab_pages = node.page_count(4096);
        let slab_bytes = slab_pages * 4096;
        let layout = Layout::from_size_align(slab_bytes, slab_bytes).unwrap();
        let base = unsafe { alloc(layout) } as usize;
        assert_ne!(base, 0);
        node.addr = base;
        node.init_header(slab_bytes);

        let obj0 = node.object_addr(0);
        assert_eq!(node.object_index_from_addr(obj0), Some(0));
        assert_eq!(node.object_index_from_addr(obj0 + 64), Some(1));
        assert_eq!(node.object_index_from_addr(obj0 + 63), None);
        assert_eq!(node.object_index_from_addr(obj0 + slab_bytes), None);

        unsafe { dealloc(base as *mut u8, layout) };
    }

    #[test]
    fn test_page_count() {
        let node8 = SlabNode::new(0, SizeClass::Bytes8);
        assert_eq!(node8.page_count(4096), 1); // SlabNode::MAX_OBJECTS * 8 = 4096

        let node64 = SlabNode::new(0, SizeClass::Bytes64);
        assert_eq!(node64.page_count(4096), 8); // SlabNode::MAX_OBJECTS * 64 = 32768

        let node2048 = SlabNode::new(0, SizeClass::Bytes2048);
        assert_eq!(node2048.page_count(4096), 256); // SlabNode::MAX_OBJECTS * 2048 = 1,048,576
    }
}
