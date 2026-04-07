//! Slab cache implementation for a single size class.
//!
//! This module implements SlabCache which manages three lists (empty, partial, full)
//! of slab nodes for a specific size class.

use log::{error, warn};

use super::slab_byte_allocator::SizeClass;
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

/// Internal deallocation result for a single size-class cache.
pub(crate) enum CacheDeallocDecision {
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

/// Slab cache for a specific size class.
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

    /// Try to allocate an object from this cache.
    ///
    /// Returns `Ok(Some(addr))` if allocation succeeds, `Ok(None)` if the cache
    /// needs the caller to provide a slab page, or an error if metadata is invalid.
    pub fn alloc_object(&mut self) -> AllocResult<Option<usize>> {
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
                return Ok(Some(obj_addr));
            }
            panic!(
                "Allocation from partial slab failed despite free_count > 0, bitmap inconsistency detected"
            );
        }

        if let Some(slab_base) = self.empty.pop_back(self.size_class) {
            let mut node = SlabNode::new(slab_base, self.size_class);
            if !node.is_valid_for_size_class() {
                return Err(AllocError::InvalidParam);
            }
            if let Some(obj_idx) = node.alloc_object() {
                let obj_addr = node.object_addr(obj_idx);
                self.partial.push_back(self.size_class, slab_base);
                return Ok(Some(obj_addr));
            }
            panic!(
                "Allocation from empty slab failed despite all objects being free, bitmap inconsistency detected"
            );
        }

        Ok(None)
    }

    /// Insert a freshly provided slab page into this cache.
    pub fn provide_slab(
        &mut self,
        slab_base: usize,
        slab_bytes: usize,
        owner_cpu: usize,
    ) -> AllocResult<()> {
        let mut node = SlabNode::new(slab_base, self.size_class);
        node.init_header(slab_bytes, owner_cpu);
        if node.free_count() == 0 {
            return Err(AllocError::InvalidParam);
        }
        self.empty.push_back(self.size_class, slab_base);
        Ok(())
    }

    /// Deallocate an object from this cache.
    pub(crate) fn dealloc_object(
        &mut self,
        obj_addr: usize,
        page_size: usize,
    ) -> CacheDeallocDecision {
        let object_size = self.size_class.size();
        let bytes_needed = SlabNode::MAX_OBJECTS * object_size;
        let page_count = bytes_needed.div_ceil(page_size);
        let slab_bytes = page_count * page_size;

        let slab_base = align_down_any(obj_addr, slab_bytes);
        let mut node = SlabNode::new(slab_base, self.size_class);
        if !node.is_valid_for_size_class() {
            warn!(
                "slab allocator: Invalid slab base {:#x} for size class {:?}",
                slab_base, self.size_class
            );
            warn!(
                "this can happen if the slab was already returned to the page allocator and the memory was reused, or if the pointer is completely invalid"
            );
            return CacheDeallocDecision::Done {
                bytes_released: 0,
                actually_deallocated: false,
            };
        }

        let was_full = node.is_full();
        let (should_release_slab, actually_freed) =
            if let Some(obj_idx) = node.object_index_from_addr(obj_addr) {
                let actually_freed = node.dealloc_object(obj_idx);
                (node.is_empty() && actually_freed, actually_freed)
            } else {
                error!("Invalid address {obj_addr:x} in slab at {slab_base:x}: not a valid object");
                return CacheDeallocDecision::Done {
                    bytes_released: 0,
                    actually_deallocated: true,
                };
            };

        if actually_freed {
            if was_full {
                self.full.remove(self.size_class, slab_base);
            } else {
                self.partial.remove(self.size_class, slab_base);
            }

            if should_release_slab {
                if self.empty.len() >= 2 {
                    return CacheDeallocDecision::ReleaseSlab {
                        slab_base,
                        page_count,
                        slab_bytes,
                        actually_deallocated: true,
                    };
                }
                self.empty.push_back(self.size_class, slab_base);
                return CacheDeallocDecision::Done {
                    bytes_released: 0,
                    actually_deallocated: true,
                };
            }

            self.partial.push_back(self.size_class, slab_base);
        }

        CacheDeallocDecision::Done {
            bytes_released: 0,
            actually_deallocated: actually_freed,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::alloc::{alloc, dealloc};
    use core::alloc::Layout;

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

        #[allow(dead_code)]
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

    fn provide_cache_slab(cache: &mut SlabCache, page_allocator: &mut MockPageAllocator) {
        let page_count = SlabNode::new(0, SizeClass::Bytes64).page_count(4096);
        let slab_bytes = page_count * 4096;
        let slab_base = page_allocator.alloc_pages(page_count, slab_bytes).unwrap();
        cache.provide_slab(slab_base, slab_bytes, 0).unwrap();
    }

    #[test]
    fn test_alloc_dealloc() {
        let mut cache = SlabCache::new(SizeClass::Bytes64);
        let mut page_allocator = MockPageAllocator::new();
        provide_cache_slab(&mut cache, &mut page_allocator);

        let obj_addr = cache.alloc_object().unwrap().unwrap();
        assert_ne!(obj_addr, 0);

        match cache.dealloc_object(obj_addr, 4096) {
            CacheDeallocDecision::Done { .. } | CacheDeallocDecision::ReleaseSlab { .. } => {}
        }
    }

    #[test]
    fn test_multiple_allocs() {
        let mut cache = SlabCache::new(SizeClass::Bytes64);
        let mut page_allocator = MockPageAllocator::new();
        provide_cache_slab(&mut cache, &mut page_allocator);

        let mut addrs = alloc::vec::Vec::new();
        for _ in 0..10 {
            let addr = cache.alloc_object().unwrap().unwrap();
            addrs.push(addr);
        }

        assert_eq!(addrs.len(), 10);

        for addr in addrs {
            cache.dealloc_object(addr, 4096);
        }
    }

    #[test]
    fn test_empty_node_management() {
        let mut cache = SlabCache::new(SizeClass::Bytes64);
        let mut page_allocator = MockPageAllocator::new();
        provide_cache_slab(&mut cache, &mut page_allocator);

        let addr1 = cache.alloc_object().unwrap().unwrap();
        cache.dealloc_object(addr1, 4096);

        let addr2 = cache.alloc_object().unwrap().unwrap();
        cache.dealloc_object(addr2, 4096);

        let addr3 = cache.alloc_object().unwrap().unwrap();
        cache.dealloc_object(addr3, 4096);

        assert!(cache.empty.len() <= 2);
    }
}
