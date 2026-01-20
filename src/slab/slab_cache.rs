//! Slab cache implementation for a single size class.
//!
//! This module implements SlabCache which manages three lists (empty, partial, full)
//! of slab nodes for a specific size class.

#[cfg(feature = "log")]
use log::{error, warn};

use super::slab_byte_allocator::{PageAllocatorForSlab as BytePageAllocator, SizeClass};
use super::slab_node::SlabNode;
use crate::{AllocError, AllocResult};

fn align_down_any(pos: usize, align: usize) -> usize {
    if align == 0 {
        return pos;
    }
    (pos / align) * align
}

struct SlabIntrusiveList {
    head: Option<usize>,
    tail: Option<usize>,
    len: usize,
}

impl SlabIntrusiveList {
    pub const fn new() -> Self {
        Self {
            head: None,
            tail: None,
            len: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn back(&self) -> Option<usize> {
        self.tail
    }

    pub fn push_back(&mut self, size_class: SizeClass, slab_base: usize) {
        let mut node = SlabNode::new(slab_base, size_class);
        node.set_prev(self.tail);
        node.set_next(None);

        if let Some(tail) = self.tail {
            let mut tail_node = SlabNode::new(tail, size_class);
            tail_node.set_next(Some(slab_base));
        } else {
            self.head = Some(slab_base);
        }

        self.tail = Some(slab_base);
        self.len += 1;
    }

    pub fn pop_back(&mut self, size_class: SizeClass) -> Option<usize> {
        let tail = self.tail?;
        self.remove(size_class, tail);
        Some(tail)
    }

    pub fn remove(&mut self, size_class: SizeClass, slab_base: usize) {
        let mut node = SlabNode::new(slab_base, size_class);
        let prev = node.prev();
        let next = node.next();

        if let Some(prev_base) = prev {
            let mut prev_node = SlabNode::new(prev_base, size_class);
            prev_node.set_next(next);
        } else {
            self.head = next;
        }

        if let Some(next_base) = next {
            let mut next_node = SlabNode::new(next_base, size_class);
            next_node.set_prev(prev);
        } else {
            self.tail = prev;
        }

        node.set_prev(None);
        node.set_next(None);
        self.len = self.len.saturating_sub(1);
    }
}

/// Slab cache for a specific size class
pub struct SlabCache {
    size_class: SizeClass,
    empty: SlabIntrusiveList,
    partial: SlabIntrusiveList,
    full: SlabIntrusiveList,
}

impl SlabCache {
    pub const fn new(size_class: SizeClass) -> Self {
        Self {
            size_class,
            empty: SlabIntrusiveList::new(),
            partial: SlabIntrusiveList::new(),
            full: SlabIntrusiveList::new(),
        }
    }

    /// Allocate an object from this cache
    /// Returns (object_addr, bytes_allocated_from_page_allocator)
    pub fn alloc_object(
        &mut self,
        page_allocator: &mut dyn BytePageAllocator,
        page_size: usize,
    ) -> AllocResult<(usize, usize)> {
        // 1. Try to allocate from partial list
        if let Some(slab_base) = self.partial.back() {
            let mut node = SlabNode::new(slab_base, self.size_class);
            if !node.is_valid_for_size_class() {
                return Err(AllocError::InvalidParam);
            }
            if let Some(obj_idx) = node.alloc_object() {
                let obj_addr = node.object_addr(obj_idx);
                if node.is_full() {
                    self.partial.remove(self.size_class, slab_base);
                    self.full.push_back(self.size_class, slab_base);
                }
                return Ok((obj_addr, 0));
            }
            panic!("Allocation from partial slab failed despite free_count > 0, bitmap inconsistency detected");
        }

        // 2. Try to allocate from empty list
        if let Some(slab_base) = self.empty.pop_back(self.size_class) {
            let mut node = SlabNode::new(slab_base, self.size_class);
            if !node.is_valid_for_size_class() {
                return Err(AllocError::InvalidParam);
            }
            if let Some(obj_idx) = node.alloc_object() {
                let obj_addr = node.object_addr(obj_idx);
                self.partial.push_back(self.size_class, slab_base);

                let prealloc_bytes = self.preallocate_empty_slab(page_allocator, page_size);
                return Ok((obj_addr, prealloc_bytes));
            }
            panic!("Allocation from empty slab failed despite all objects being free, bitmap inconsistency detected");
        }

        // 3. Allocate a new node from page allocator
        let (obj_addr, bytes) = self.allocate_new_slab(page_allocator, page_size)?;
        Ok((obj_addr, bytes))
    }

    /// Allocate a new slab from page allocator
    /// Returns (object_addr, bytes_allocated_from_page_allocator)
    fn allocate_new_slab(
        &mut self,
        page_allocator: &mut dyn BytePageAllocator,
        page_size: usize,
    ) -> AllocResult<(usize, usize)> {
        let object_size = self.size_class.size();
        let bytes_needed = SlabNode::MAX_OBJECTS * object_size;
        let page_count = (bytes_needed + page_size - 1) / page_size;
        let slab_bytes = page_count * page_size;

        let start_addr = page_allocator.alloc_pages(page_count, slab_bytes)?;

        let mut new_node = SlabNode::new(start_addr, self.size_class);
        new_node.init_header(slab_bytes);

        if let Some(obj_idx) = new_node.alloc_object() {
            let obj_addr = new_node.object_addr(obj_idx);
            self.partial.push_back(self.size_class, start_addr);

            let prealloc_bytes = self.preallocate_empty_slab(page_allocator, page_size);
            return Ok((obj_addr, slab_bytes + prealloc_bytes));
        }

        // This should never happen - newly initialized slab must have at least one free object
        panic!("Failed to allocate from newly initialized slab: bitmap inconsistency or corruption detected");
    }

    /// Pre-allocate an empty slab for future allocations
    /// Returns bytes allocated from page allocator (0 if already has empty nodes)
    fn preallocate_empty_slab(
        &mut self,
        page_allocator: &mut dyn BytePageAllocator,
        page_size: usize,
    ) -> usize {
        if self.empty.len() > 0 {
            return 0;
        }

        let object_size = self.size_class.size();
        let bytes_needed = SlabNode::MAX_OBJECTS * object_size;
        let page_count = (bytes_needed + page_size - 1) / page_size;
        let slab_bytes = page_count * page_size;

        if let Ok(start_addr) = page_allocator.alloc_pages(page_count, slab_bytes) {
            let mut new_node = SlabNode::new(start_addr, self.size_class);
            new_node.init_header(slab_bytes);
            self.empty.push_back(self.size_class, start_addr);
            return slab_bytes;
        }

        0
    }

    /// Deallocate an object
    /// Returns (bytes_freed_from_page_allocator, actually_deallocated)
    /// actually_deallocated is false if this was a double-free
    pub fn dealloc_object(
        &mut self,
        obj_addr: usize,
        page_allocator: &mut dyn BytePageAllocator,
        page_size: usize,
    ) -> (usize, bool) {
        let object_size = self.size_class.size();
        let bytes_needed = SlabNode::MAX_OBJECTS * object_size;
        let page_count = (bytes_needed + page_size - 1) / page_size;
        let slab_bytes = page_count * page_size;

        let slab_base = align_down_any(obj_addr, slab_bytes);
        let mut node = SlabNode::new(slab_base, self.size_class);
        if !node.is_valid_for_size_class() {
            // This can happen if the slab was already returned to the page allocator
            // and the memory was reused, or if the pointer is completely invalid.
            // For robustness, especially in double-free tests, we return false.
            warn!(
                "slab allocator: Invalid slab base {:#x} for size class {:?}",
                slab_base, self.size_class
            );
            warn!("this can happen if the slab was already returned to the page allocator and the memory was reused, 
                or if the pointer is completely invalid");
            return (0, false);
        }

        let was_full = node.is_full();
        let (should_dealloc_slab, actually_freed) =
            if let Some(obj_idx) = node.object_index_from_addr(obj_addr) {
                // dealloc_object returns true if object was allocated, false if already free (double-free)
                let actually_freed = node.dealloc_object(obj_idx);
                (node.is_empty() && actually_freed, actually_freed)
            } else {
                error!(
                    "Invalid address {:x} in slab at {:x}: not a valid object",
                    obj_addr, slab_base
                );
                return (0, true); // Not a double-free, just invalid address (treat as no-op)
            };

        // Only manipulate lists if this was not a double-free
        if actually_freed {
            // Remove slab from its current list before moving or deallocating it
            if was_full {
                self.full.remove(self.size_class, slab_base);
            } else {
                self.partial.remove(self.size_class, slab_base);
            }

            if should_dealloc_slab {
                // Slab became empty - either deallocate or move to empty list
                if self.empty.len() >= 2 {
                    page_allocator.dealloc_pages(slab_base, page_count);
                    return (slab_bytes, true);
                } else {
                    self.empty.push_back(self.size_class, slab_base);
                    return (0, true);
                }
            }

            // Slab still has objects - if it was full, it's now partial
            if was_full {
                self.partial.push_back(self.size_class, slab_base);
            }
        }

        (0, actually_freed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::alloc::{alloc, dealloc};
    use core::alloc::Layout;

    // Re-import SizeClass for tests
    use super::super::slab_byte_allocator::SizeClass;

    struct MockPageAllocator {
        allocated: alloc::vec::Vec<(usize, Layout, usize)>,
    }

    impl MockPageAllocator {
        fn new() -> Self {
            Self {
                allocated: alloc::vec::Vec::new(),
            }
        }
    }

    impl BytePageAllocator for MockPageAllocator {
        fn alloc_pages(&mut self, num_pages: usize, alignment: usize) -> AllocResult<usize> {
            let size = num_pages * 4096;
            let layout =
                Layout::from_size_align(size, alignment).map_err(|_| AllocError::InvalidParam)?;
            let addr = unsafe { alloc(layout) } as usize;
            if addr == 0 {
                return Err(AllocError::NoMemory);
            }
            self.allocated.push((addr, layout, num_pages));
            Ok(addr)
        }

        fn dealloc_pages(&mut self, pos: usize, num_pages: usize) {
            if let Some(idx) = self
                .allocated
                .iter()
                .position(|&(addr, _layout, count)| addr == pos && count == num_pages)
            {
                let (_addr, layout, _count) = self.allocated.swap_remove(idx);
                unsafe { dealloc(pos as *mut u8, layout) };
            }
        }
    }

    #[test]
    fn test_alloc_dealloc() {
        let mut cache = SlabCache::new(SizeClass::Bytes64);
        let mut page_allocator = MockPageAllocator::new();

        let (obj_addr, _) = cache.alloc_object(&mut page_allocator, 4096).unwrap();

        assert_ne!(obj_addr, 0);

        cache.dealloc_object(obj_addr, &mut page_allocator, 4096);
    }

    #[test]
    fn test_multiple_allocs() {
        let mut cache = SlabCache::new(SizeClass::Bytes64);
        let mut page_allocator = MockPageAllocator::new();

        let mut addrs = alloc::vec::Vec::new();
        for _ in 0..10 {
            let (addr, _) = cache.alloc_object(&mut page_allocator, 4096).unwrap();
            addrs.push(addr);
        }

        assert_eq!(addrs.len(), 10);

        for addr in addrs {
            cache.dealloc_object(addr, &mut page_allocator, 4096);
        }
    }

    #[test]
    fn test_empty_node_management() {
        let mut cache = SlabCache::new(SizeClass::Bytes64);
        let mut page_allocator = MockPageAllocator::new();

        let (addr1, _) = cache.alloc_object(&mut page_allocator, 4096).unwrap();
        cache.dealloc_object(addr1, &mut page_allocator, 4096);

        let (addr2, _) = cache.alloc_object(&mut page_allocator, 4096).unwrap();
        cache.dealloc_object(addr2, &mut page_allocator, 4096);

        let (addr3, _) = cache.alloc_object(&mut page_allocator, 4096).unwrap();
        cache.dealloc_object(addr3, &mut page_allocator, 4096);

        assert!(cache.empty.len() <= 2);
    }
}
