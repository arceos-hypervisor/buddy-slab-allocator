//! Slab byte allocator implementation.
//!
//! This module implements an improved slab allocator for small object allocation
//! with pooled linked lists, inspired by asterinas design.

use core::alloc::Layout;
use core::ptr::NonNull;

use log::warn;

use crate::{AllocError, AllocResult};

use super::slab_cache::CacheDeallocDecision;
pub use super::slab_cache::SlabCache;
pub use super::slab_node::SlabNode;

/// Size classes for slab allocation.
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

    pub fn page_count(&self, page_size: usize) -> usize {
        SlabNode::new(0, *self).page_count(page_size)
    }

    pub fn slab_bytes(&self, page_size: usize) -> usize {
        self.page_count(page_size) * page_size
    }
}

pub enum SlabAllocDecision {
    Allocated(NonNull<u8>, usize),
    NeedsRefill {
        size_class: SizeClass,
        page_count: usize,
        slab_bytes: usize,
    },
}

pub enum SlabDeallocDecision {
    Done {
        bytes_released: usize,
        actually_deallocated: bool,
    },
    ReleaseSlab {
        slab_base: usize,
        page_count: usize,
        slab_bytes: usize,
        actually_deallocated: bool,
    },
}

/// Slab byte allocator with pooled linked lists.
pub struct SlabByteAllocator<const PAGE_SIZE: usize = { crate::DEFAULT_PAGE_SIZE }> {
    caches: [SlabCache; SizeClass::COUNT],
    total_bytes: usize,
    allocated_bytes: usize,
}

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
            total_bytes: 0,
            allocated_bytes: 0,
        }
    }

    pub fn alloc(&mut self, layout: Layout) -> AllocResult<SlabAllocDecision> {
        let size_class = SizeClass::from_layout(layout).ok_or(AllocError::InvalidParam)?;
        let cache = &mut self.caches[size_class.to_index()];

        if let Some(obj_addr) = cache.alloc_object()? {
            self.allocated_bytes += layout.size().max(layout.align());
            return Ok(SlabAllocDecision::Allocated(
                unsafe { NonNull::new_unchecked(obj_addr as *mut u8) },
                0,
            ));
        }

        Ok(SlabAllocDecision::NeedsRefill {
            size_class,
            page_count: size_class.page_count(PAGE_SIZE),
            slab_bytes: size_class.slab_bytes(PAGE_SIZE),
        })
    }

    pub fn provide_slab(
        &mut self,
        size_class: SizeClass,
        owner_cpu: usize,
        slab_base: usize,
        slab_bytes: usize,
    ) -> AllocResult<()> {
        self.caches[size_class.to_index()].provide_slab(slab_base, slab_bytes, owner_cpu)?;
        self.total_bytes += slab_bytes;
        Ok(())
    }

    pub fn dealloc(&mut self, ptr: NonNull<u8>, layout: Layout) -> SlabDeallocDecision {
        let Some(size_class) = SizeClass::from_layout(layout) else {
            warn!(
                "Invalid layout during slab dealloc: size={}, align={}",
                layout.size(),
                layout.align()
            );
            return SlabDeallocDecision::Done {
                bytes_released: 0,
                actually_deallocated: false,
            };
        };

        let decision =
            self.caches[size_class.to_index()].dealloc_object(ptr.as_ptr() as usize, PAGE_SIZE);

        match decision {
            CacheDeallocDecision::Done {
                bytes_released,
                actually_deallocated,
            } => {
                if actually_deallocated {
                    self.allocated_bytes = self
                        .allocated_bytes
                        .saturating_sub(layout.size().max(layout.align()));
                }
                SlabDeallocDecision::Done {
                    bytes_released,
                    actually_deallocated,
                }
            }
            CacheDeallocDecision::ReleaseSlab {
                slab_base,
                page_count,
                slab_bytes,
                actually_deallocated,
            } => {
                if actually_deallocated {
                    self.allocated_bytes = self
                        .allocated_bytes
                        .saturating_sub(layout.size().max(layout.align()));
                }
                self.total_bytes = self.total_bytes.saturating_sub(slab_bytes);
                SlabDeallocDecision::ReleaseSlab {
                    slab_base,
                    page_count,
                    slab_bytes,
                    actually_deallocated,
                }
            }
        }
    }

    pub fn owner_cpu_of(&self, ptr: NonNull<u8>, layout: Layout) -> Option<usize> {
        let size_class = SizeClass::from_layout(layout)?;
        let slab_bytes = size_class.slab_bytes(PAGE_SIZE);
        let slab_base = (ptr.as_ptr() as usize / slab_bytes) * slab_bytes;
        let node = SlabNode::new(slab_base, size_class);
        if node.is_valid_for_size_class() {
            Some(node.owner_cpu())
        } else {
            None
        }
    }

    pub fn total_bytes(&self) -> usize {
        self.total_bytes
    }

    pub fn used_bytes(&self) -> usize {
        self.allocated_bytes
    }

    pub fn available_bytes(&self) -> usize {
        self.total_bytes.saturating_sub(self.allocated_bytes)
    }
}

impl<const PAGE_SIZE: usize> Default for SlabByteAllocator<PAGE_SIZE> {
    fn default() -> Self {
        Self::new()
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
        assert_eq!(
            SizeClass::from_layout(Layout::from_size_align(64, 4096).unwrap()),
            None
        );
    }
}
