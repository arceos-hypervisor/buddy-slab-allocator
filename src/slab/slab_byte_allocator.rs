//! Slab byte allocator implementation for Axvisor.
//!
//! This module implements an improved slab allocator for small object allocation
//! with pooled linked lists, inspired by asterinas design.

use core::alloc::Layout;
use core::ptr::NonNull;

#[cfg(feature = "log")]
use log::warn;

use crate::{AllocError, AllocResult, ByteAllocator};

// Re-export public types from sibling modules
pub use super::slab_cache::SlabCache;
pub use super::slab_node::SlabNode;

/// Size classes for slab allocation
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(usize)]
pub enum SizeClass {
    Bytes8 = 8,
    Bytes16 = 16,
    Bytes32 = 32,
    Bytes64 = 64,
    Bytes128 = 128,
    Bytes256 = 256,
    Bytes512 = 512,
    Bytes1024 = 1024,
    Bytes2048 = 2048,
}

impl SizeClass {
    pub const COUNT: usize = 9;
    const MAX_OBJ_SIZE: usize = 2048;

    /// Select size class from memory layout
    pub fn from_layout(layout: Layout) -> Option<Self> {
        let required_size = layout.size().max(layout.align());

        if required_size > Self::MAX_OBJ_SIZE {
            warn!(
                "Invalid layout: size={}, align={}",
                layout.size(),
                layout.align()
            );
            return None;
        }

        Some(match required_size {
            0..=8 => SizeClass::Bytes8,
            9..=16 => SizeClass::Bytes16,
            17..=32 => SizeClass::Bytes32,
            33..=64 => SizeClass::Bytes64,
            65..=128 => SizeClass::Bytes128,
            129..=256 => SizeClass::Bytes256,
            257..=512 => SizeClass::Bytes512,
            513..=1024 => SizeClass::Bytes1024,
            1025..=2048 => SizeClass::Bytes2048,
            _ => unreachable!(
                "Invalid layout: size={}, align={}",
                layout.size(),
                layout.align()
            ),
        })
    }

    pub fn size(&self) -> usize {
        *self as usize
    }

    pub fn to_index(&self) -> usize {
        match self {
            SizeClass::Bytes8 => 0,
            SizeClass::Bytes16 => 1,
            SizeClass::Bytes32 => 2,
            SizeClass::Bytes64 => 3,
            SizeClass::Bytes128 => 4,
            SizeClass::Bytes256 => 5,
            SizeClass::Bytes512 => 6,
            SizeClass::Bytes1024 => 7,
            SizeClass::Bytes2048 => 8,
        }
    }

    pub fn from_index(index: usize) -> Option<Self> {
        match index {
            0 => Some(SizeClass::Bytes8),
            1 => Some(SizeClass::Bytes16),
            2 => Some(SizeClass::Bytes32),
            3 => Some(SizeClass::Bytes64),
            4 => Some(SizeClass::Bytes128),
            5 => Some(SizeClass::Bytes256),
            6 => Some(SizeClass::Bytes512),
            7 => Some(SizeClass::Bytes1024),
            8 => Some(SizeClass::Bytes2048),
            _ => None,
        }
    }
}

/// Page allocator trait for slab allocator
pub trait PageAllocatorForSlab {
    fn alloc_pages(&mut self, num_pages: usize, alignment: usize) -> AllocResult<usize>;
    fn dealloc_pages(&mut self, pos: usize, num_pages: usize);
}

/// Slab byte allocator with pooled linked lists
pub struct SlabByteAllocator<const PAGE_SIZE: usize = { crate::DEFAULT_PAGE_SIZE }> {
    caches: [SlabCache; SizeClass::COUNT],
    page_allocator: Option<*mut dyn PageAllocatorForSlab>,
    total_bytes: usize,
    allocated_bytes: usize,
}

// SAFETY: SlabByteAllocator is used behind SpinNoIrq locks
unsafe impl<const PAGE_SIZE: usize> Send for SlabByteAllocator<PAGE_SIZE> {}
unsafe impl<const PAGE_SIZE: usize> Sync for SlabByteAllocator<PAGE_SIZE> {}

impl<const PAGE_SIZE: usize> SlabByteAllocator<PAGE_SIZE> {
    pub const fn new() -> Self {
        Self {
            caches: [
                SlabCache::new(SizeClass::Bytes8),
                SlabCache::new(SizeClass::Bytes16),
                SlabCache::new(SizeClass::Bytes32),
                SlabCache::new(SizeClass::Bytes64),
                SlabCache::new(SizeClass::Bytes128),
                SlabCache::new(SizeClass::Bytes256),
                SlabCache::new(SizeClass::Bytes512),
                SlabCache::new(SizeClass::Bytes1024),
                SlabCache::new(SizeClass::Bytes2048),
            ],
            page_allocator: None,
            total_bytes: 0,
            allocated_bytes: 0,
        }
    }

    /// Initialize the allocator
    pub fn init(&mut self) {}

    pub fn set_page_allocator(&mut self, page_allocator: *mut dyn PageAllocatorForSlab) {
        self.page_allocator = Some(page_allocator);
    }
}

impl<const PAGE_SIZE: usize> Default for SlabByteAllocator<PAGE_SIZE> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const PAGE_SIZE: usize> ByteAllocator for SlabByteAllocator<PAGE_SIZE> {
    fn alloc(&mut self, layout: Layout) -> AllocResult<NonNull<u8>> {
        let size_class = SizeClass::from_layout(layout).ok_or(AllocError::InvalidParam)?;

        let Some(page_allocator_ptr) = self.page_allocator else {
            return Err(AllocError::NoMemory);
        };

        let page_allocator = unsafe { &mut *page_allocator_ptr };
        let cache = &mut self.caches[size_class.to_index()];

        let (obj_addr, page_bytes) = cache.alloc_object(page_allocator, PAGE_SIZE)?;
        self.allocated_bytes += layout.size().max(layout.align());
        self.total_bytes += page_bytes;

        Ok(unsafe { NonNull::new_unchecked(obj_addr as *mut u8) })
    }

    fn dealloc(&mut self, ptr: NonNull<u8>, layout: Layout) {
        let size_class = SizeClass::from_layout(layout).expect("Invalid layout");
        let obj_addr = ptr.as_ptr() as usize;

        let Some(page_allocator_ptr) = self.page_allocator else {
            return;
        };

        let page_allocator = unsafe { &mut *page_allocator_ptr };
        let cache = &mut self.caches[size_class.to_index()];

        let (freed_bytes, actually_freed) =
            cache.dealloc_object(obj_addr, page_allocator, PAGE_SIZE);

        // Only update allocated_bytes if this was not a double-free
        if actually_freed {
            self.allocated_bytes = self
                .allocated_bytes
                .saturating_sub(layout.size().max(layout.align()));
        }
        self.total_bytes = self.total_bytes.saturating_sub(freed_bytes);
    }

    fn total_bytes(&self) -> usize {
        self.total_bytes
    }

    fn used_bytes(&self) -> usize {
        self.allocated_bytes
    }

    fn available_bytes(&self) -> usize {
        self.total_bytes.saturating_sub(self.allocated_bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_size_class() {
        assert_eq!(
            SizeClass::from_layout(Layout::from_size_align(8, 8).unwrap()),
            Some(SizeClass::Bytes8)
        );
        assert_eq!(
            SizeClass::from_layout(Layout::from_size_align(16, 8).unwrap()),
            Some(SizeClass::Bytes16)
        );
        assert_eq!(
            SizeClass::from_layout(Layout::from_size_align(2048, 8).unwrap()),
            Some(SizeClass::Bytes2048)
        );
        assert_eq!(
            SizeClass::from_layout(Layout::from_size_align(2049, 8).unwrap()),
            None
        );
    }

    #[test]
    fn test_size_class_boundaries() {
        // Test all size class boundaries
        assert_eq!(SizeClass::Bytes8.size(), 8);
        assert_eq!(SizeClass::Bytes16.size(), 16);
        assert_eq!(SizeClass::Bytes32.size(), 32);
        assert_eq!(SizeClass::Bytes64.size(), 64);
        assert_eq!(SizeClass::Bytes128.size(), 128);
        assert_eq!(SizeClass::Bytes256.size(), 256);
        assert_eq!(SizeClass::Bytes512.size(), 512);
        assert_eq!(SizeClass::Bytes1024.size(), 1024);
        assert_eq!(SizeClass::Bytes2048.size(), 2048);
    }

    #[test]
    fn test_size_class_alignment_limits() {
        // Alignment too large should return None
        assert_eq!(
            SizeClass::from_layout(Layout::from_size_align(64, 4096).unwrap()),
            None
        );
    }
}
