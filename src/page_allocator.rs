//! Page allocator with contiguous block combination support.

use crate::buddy::{BuddyPageAllocator, DEFAULT_MAX_ORDER};
use crate::{AllocError, AllocResult, BaseAllocator, PageAllocator};

#[cfg(feature = "log")]
use log::{debug, warn};

/// Maximum number of buddy blocks in a single contiguous allocation
const MAX_PARTS_PER_ALLOC: usize = 8;

/// Maximum number of concurrent composite allocations tracked
const MAX_COMPOSITE_ALLOCS: usize = 16;

/// Metadata for a composite allocation (multiple buddy blocks combined)
#[derive(Clone, Copy, Debug)]
struct CompositeBlockInfo {
    /// Base address of the composite allocation
    base_addr: usize,
    /// Number of parts in this composite allocation
    part_count: u8,
    /// Individual parts: (address, order)
    parts: [(usize, u32); MAX_PARTS_PER_ALLOC],
}

/// Tracker for composite allocations using fixed-size array
struct CompositeBlockTracker {
    /// Array to store composite block metadata
    blocks: [Option<CompositeBlockInfo>; MAX_COMPOSITE_ALLOCS],
    /// Number of active composite allocations
    count: usize,
}

impl CompositeBlockTracker {
    const fn new() -> Self {
        Self {
            blocks: [None; MAX_COMPOSITE_ALLOCS],
            count: 0,
        }
    }

    /// Insert a new composite block
    ///
    /// Returns false if the tracker is full
    fn insert(&mut self, base_addr: usize, parts: &[(usize, u32)], part_count: usize) -> bool {
        if self.count >= MAX_COMPOSITE_ALLOCS {
            return false;
        }

        let mut info = CompositeBlockInfo {
            base_addr,
            part_count: part_count as u8,
            parts: [(0, 0); MAX_PARTS_PER_ALLOC],
        };

        for i in 0..part_count {
            info.parts[i] = parts[i];
        }

        self.blocks[self.count] = Some(info);
        self.count += 1;
        true
    }

    /// Find a composite block by its base address
    fn find(&self, base_addr: usize) -> Option<CompositeBlockInfo> {
        for i in 0..self.count {
            if let Some(info) = self.blocks[i] {
                if info.base_addr == base_addr {
                    return Some(info);
                }
            }
        }
        None
    }

    /// Remove a composite block by its base address
    ///
    /// Returns true if the block was found and removed
    fn remove(&mut self, base_addr: usize) -> bool {
        for i in 0..self.count {
            if let Some(info) = self.blocks[i] {
                if info.base_addr == base_addr {
                    // Move the last element to this position to keep array compact
                    if i < self.count - 1 {
                        self.blocks[i] = self.blocks[self.count - 1];
                    }
                    self.blocks[self.count - 1] = None;
                    self.count -= 1;
                    return true;
                }
            }
        }
        false
    }
}

pub struct CompositePageAllocator<const PAGE_SIZE: usize = { crate::DEFAULT_PAGE_SIZE }> {
    /// Underlying buddy allocator for standard allocations
    buddy: BuddyPageAllocator<PAGE_SIZE>,
    /// Tracker for composite allocations (multiple buddy blocks combined)
    composite_tracker: CompositeBlockTracker,
}

impl<const PAGE_SIZE: usize> CompositePageAllocator<PAGE_SIZE> {
    /// Create a new page allocator with contiguous block support
    pub const fn new() -> Self {
        Self {
            buddy: BuddyPageAllocator::<PAGE_SIZE>::new(),
            composite_tracker: CompositeBlockTracker::new(),
        }
    }

    /// Set the address translator so that the underlying buddy allocator can
    /// reason about physical address ranges (e.g. low-memory regions).
    pub fn set_addr_translator(&mut self, translator: &'static dyn crate::AddrTranslator) {
        self.buddy.set_addr_translator(translator);
    }

    /// Allocate low-memory pages (physical address < 4GiB).
    /// This is a thin wrapper over the buddy allocator's lowmem allocation.
    pub fn alloc_pages_lowmem(&mut self, num_pages: usize, alignment: usize) -> AllocResult<usize> {
        self.buddy.alloc_pages_lowmem(num_pages, alignment)
    }

    /// Try to find and allocate contiguous small blocks from buddy free lists.
    ///
    /// This method searches buddy free lists for contiguous blocks that can satisfy
    /// the allocation request. It uses the sorted nature of free lists to efficiently
    /// check for contiguity.
    ///
    /// # Algorithm
    /// 1. Iterate through free lists from largest to smallest blocks
    /// 2. For each block, check if it's contiguous with already collected blocks
    /// 3. Collect contiguous blocks until we have enough pages
    /// 4. If successful, allocate all collected blocks
    ///
    /// # Returns
    /// Base address of the first block if contiguous blocks found, otherwise None
    fn try_combine_contiguous_blocks(
        &mut self,
        num_pages: usize,
        alignment: usize,
    ) -> Option<usize> {
        let mut remaining_pages = num_pages;
        let mut contiguous_blocks: [(usize, u32); MAX_PARTS_PER_ALLOC] =
            [(0, 0); MAX_PARTS_PER_ALLOC];
        let mut block_count = 0;
        let mut min_addr = usize::MAX;
        let mut max_addr = 0;

        // Iterate from largest to smallest blocks
        for order in (0..=DEFAULT_MAX_ORDER).rev() {
            let block_pages = 1usize << order;

            if remaining_pages == 0 || block_count >= MAX_PARTS_PER_ALLOC {
                break;
            }

            // Get free blocks of this order from all zones
            for zone_id in 0..self.buddy.get_zone_count() {
                if let Some(blocks) = self.buddy.get_free_blocks_by_order(zone_id, order as u32) {
                    // Iterate through sorted free blocks
                    for block in blocks {
                        if block_count >= MAX_PARTS_PER_ALLOC {
                            break;
                        }

                        let block_start = block.addr;
                        let block_end = block_start + block_pages * PAGE_SIZE;

                        // Check alignment requirement
                        if !crate::is_aligned(block_start, alignment) {
                            continue;
                        }

                        // Check contiguity with existing blocks
                        if block_count == 0 {
                            // First block - just record it
                            contiguous_blocks[block_count] = (block_start, order as u32);
                            min_addr = block_start;
                            max_addr = block_end;
                            block_count += 1;
                            remaining_pages -= block_pages.min(remaining_pages);
                        } else {
                            if block_end == min_addr {
                                // Block is to the left, update min_addr
                                contiguous_blocks[block_count] = (block_start, order as u32);
                                min_addr = block_start;
                                block_count += 1;
                                remaining_pages -= block_pages.min(remaining_pages);
                            } else if block_start == max_addr {
                                // Block is to the right, update max_addr
                                contiguous_blocks[block_count] = (block_start, order as u32);
                                max_addr = block_end;
                                block_count += 1;
                                remaining_pages -= block_pages.min(remaining_pages);
                            }
                        }

                        if remaining_pages == 0 {
                            break;
                        }
                    }
                }

                if remaining_pages == 0 {
                    break;
                }
            }
        }

        // If we found enough contiguous pages, allocate them
        if remaining_pages == 0 {
            let mut parts = [(0usize, 0u32); MAX_PARTS_PER_ALLOC];

            // Allocate all contiguous blocks
            for i in 0..block_count {
                let (addr, order) = contiguous_blocks[i];
                let block_pages = 1usize << order;

                debug!(
                    "Block {}: addr={:#x}, order={}, pages={}, size={} MB",
                    i,
                    addr,
                    order,
                    block_pages,
                    (block_pages * PAGE_SIZE) / (1024 * 1024)
                );

                // Allocate this specific block
                if let Err(_e) = self.buddy.alloc_pages_at(addr, block_pages, alignment) {
                    // Allocation failed, rollback
                    warn!("Contiguous block allocation failed at {}, rolling back", i);
                    for j in 0..i {
                        let (dealloc_addr, dealloc_order) = parts[j];
                        let dealloc_pages = 1usize << dealloc_order;
                        self.buddy.dealloc_pages(dealloc_addr, dealloc_pages);
                    }
                    return None;
                }

                parts[i] = (addr, order);
            }

            // Assertion: allocated pages must be >= requested pages
            let actual_pages: usize = parts[..block_count]
                .iter()
                .map(|(_, order)| 1usize << *order as usize)
                .sum();
            debug_assert!(
                actual_pages >= num_pages,
                "Allocated pages {} < requested pages {}",
                actual_pages,
                num_pages
            );

            // Save metadata to tracker for proper deallocation
            if !self
                .composite_tracker
                .insert(min_addr, &parts[..block_count], block_count)
            {
                // Tracker is full, rollback and fail
                warn!("Composite tracker full, rolling back allocation");
                for j in 0..block_count {
                    let (dealloc_addr, dealloc_order) = parts[j];
                    let dealloc_pages = 1usize << dealloc_order;
                    self.buddy.dealloc_pages(dealloc_addr, dealloc_pages);
                }
                return None;
            }

            debug!("Contiguous block allocation succeeded: base_addr={:#x}, pages={}, parts={}, actual_pages={}",
                  min_addr, num_pages, block_count, actual_pages);

            return Some(min_addr);
        }

        None
    }

    /// Print detailed statistics when allocation fails.
    ///
    /// This function delegates to buddy allocator's detailed statistics reporter.
    #[cfg(feature = "tracking")]
    fn print_alloc_failure_stats(&self, num_pages: usize, alignment: usize) {
        self.buddy.print_alloc_failure_stats(num_pages, alignment);
    }

    #[cfg(not(feature = "tracking"))]
    fn print_alloc_failure_stats(&self, _num_pages: usize, _alignment: usize) {
        // No-op when tracking is disabled
    }
}

impl<const PAGE_SIZE: usize> PageAllocator for CompositePageAllocator<PAGE_SIZE> {
    const PAGE_SIZE: usize = PAGE_SIZE;

    fn alloc_pages(&mut self, num_pages: usize, alignment: usize) -> AllocResult<usize> {
        if num_pages == 0 {
            return Err(AllocError::InvalidParam);
        }

        let buddy_pages = if num_pages.is_power_of_two() {
            num_pages
        } else {
            num_pages.next_power_of_two()
        };

        // Try to allocate from buddy system first
        let base_addr = match self.buddy.alloc_pages(buddy_pages, alignment) {
            Ok(addr) => addr,
            Err(_) => {
                // Standard allocation failed, try contiguous block combination
                debug!(
                    "Standard allocation failed, trying contiguous block combination for {} pages",
                    num_pages
                );
                if let Some(addr) = self.try_combine_contiguous_blocks(num_pages, alignment) {
                    return Ok(addr);
                }
                self.print_alloc_failure_stats(num_pages, alignment);
                return Err(AllocError::NoMemory);
            }
        };

        Ok(base_addr)
    }

    fn dealloc_pages(&mut self, pos: usize, num_pages: usize) {
        if num_pages == 0 {
            return;
        }

        // Check if this is a composite allocation
        if let Some(info) = self.composite_tracker.find(pos) {
            // Composite block: deallocate each part separately
            debug!(
                "Deallocating composite block: base_addr={:#x}, part_count={}",
                pos, info.part_count
            );

            for i in 0..info.part_count as usize {
                let (addr, order) = info.parts[i];
                let pages = 1usize << order;
                debug!(
                    "  Part {}: addr={:#x}, order={}, pages={}",
                    i, addr, order, pages
                );
                self.buddy.dealloc_pages(addr, pages);
            }

            // Remove from tracker
            self.composite_tracker.remove(pos);
        } else {
            // Regular buddy block: deallocate directly
            if num_pages.is_power_of_two() {
                self.buddy.dealloc_pages(pos, num_pages);
            } else {
                self.buddy.dealloc_pages(pos, num_pages.next_power_of_two());
            }
        }
    }

    /// Allocate contiguous memory pages at a specific address.
    ///
    /// Delegates to buddy allocator.
    fn alloc_pages_at(
        &mut self,
        base: usize,
        num_pages: usize,
        alignment: usize,
    ) -> AllocResult<usize> {
        self.buddy.alloc_pages_at(base, num_pages, alignment)
    }

    /// Return total number of memory pages.
    fn total_pages(&self) -> usize {
        self.buddy.total_pages()
    }

    /// Return number of allocated memory pages.
    fn used_pages(&self) -> usize {
        self.buddy.used_pages()
    }

    /// Return number of available memory pages.
    fn available_pages(&self) -> usize {
        self.buddy.available_pages()
    }
}

impl<const PAGE_SIZE: usize> CompositePageAllocator<PAGE_SIZE> {
    /// Get buddy allocator statistics
    #[cfg(feature = "tracking")]
    pub fn get_buddy_stats(&self) -> crate::buddy::BuddyStats {
        self.buddy.get_stats()
    }
}

impl<const PAGE_SIZE: usize> BaseAllocator for CompositePageAllocator<PAGE_SIZE> {
    /// Initialize the allocator with a free memory region.
    fn init(&mut self, start: usize, size: usize) {
        self.buddy.init(start, size);
    }

    /// Add a free memory region to the allocator.
    fn add_memory(&mut self, start: usize, size: usize) -> AllocResult<()> {
        self.buddy.add_memory(start, size)
    }
}

// Implement PageAllocatorForSlab for CompositePageAllocator
impl<const PAGE_SIZE: usize> crate::slab::PageAllocatorForSlab
    for CompositePageAllocator<PAGE_SIZE>
{
    fn alloc_pages(&mut self, num_pages: usize, alignment: usize) -> AllocResult<usize> {
        <Self as PageAllocator>::alloc_pages(self, num_pages, alignment)
    }

    fn dealloc_pages(&mut self, pos: usize, num_pages: usize) {
        <Self as PageAllocator>::dealloc_pages(self, pos, num_pages)
    }
}

impl<const PAGE_SIZE: usize> Default for CompositePageAllocator<PAGE_SIZE> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_composite_block_tracker() {
        let mut tracker = CompositeBlockTracker::new();

        // Test insertion
        let parts = [(0x1000, 3), (0x2000, 2)];
        assert!(tracker.insert(0x1000, &parts, 2));
        assert_eq!(tracker.count, 1);

        // Test finding
        let info = tracker.find(0x1000);
        assert!(info.is_some());
        let info = info.unwrap();
        assert_eq!(info.base_addr, 0x1000);
        assert_eq!(info.part_count, 2);
        assert_eq!(info.parts[0], (0x1000, 3));
        assert_eq!(info.parts[1], (0x2000, 2));

        // Test removal
        assert!(tracker.remove(0x1000));
        assert_eq!(tracker.count, 0);
        assert!(tracker.find(0x1000).is_none());
    }

    #[test]
    fn test_composite_block_tracker_capacity() {
        let mut tracker = CompositeBlockTracker::new();

        // Fill the tracker to capacity
        for i in 0..MAX_COMPOSITE_ALLOCS {
            let parts = [(0x1000 + i * 0x1000, 3)];
            assert!(tracker.insert(0x1000 + i * 0x1000, &parts, 1));
        }

        assert_eq!(tracker.count, MAX_COMPOSITE_ALLOCS);

        // Try to insert one more - should fail
        let parts = [(0x10000, 3)];
        assert!(!tracker.insert(0x10000, &parts, 1));

        // Remove one and verify we can insert again
        assert!(tracker.remove(0x1000));
        assert!(tracker.insert(0x10000, &parts, 1));
    }

    #[test]
    fn test_composite_tracker_find_nonexistent() {
        let tracker = CompositeBlockTracker::new();
        assert!(tracker.find(0x1000).is_none());
    }

    #[test]
    fn test_composite_tracker_remove_nonexistent() {
        let mut tracker = CompositeBlockTracker::new();
        assert!(!tracker.remove(0x1000));
    }

    #[test]
    fn test_composite_tracker_multiple_blocks() {
        let mut tracker = CompositeBlockTracker::new();

        let parts1 = [(0x1000, 3), (0x2000, 2)];
        let parts2 = [(0x3000, 4), (0x4000, 3), (0x5000, 2)];

        tracker.insert(0x1000, &parts1, 2);
        tracker.insert(0x3000, &parts2, 3);

        assert_eq!(tracker.count, 2);

        let info1 = tracker.find(0x1000);
        assert!(info1.is_some());
        assert_eq!(info1.unwrap().part_count, 2);

        let info2 = tracker.find(0x3000);
        assert!(info2.is_some());
        assert_eq!(info2.unwrap().part_count, 3);
    }
}

#[cfg(test)]
mod unit_tests {
    use super::*;
    use alloc::alloc::{alloc, dealloc};
    use core::alloc::Layout;

    const TEST_HEAP_SIZE: usize = 16 * 1024 * 1024;
    const TEST_PAGE_SIZE: usize = 0x1000;

    fn alloc_test_heap(size: usize) -> (*mut u8, Layout) {
        let layout = Layout::from_size_align(size, TEST_PAGE_SIZE).unwrap();
        let ptr = unsafe { alloc(layout) };
        assert!(!ptr.is_null());
        (ptr, layout)
    }

    fn dealloc_test_heap(ptr: *mut u8, layout: Layout) {
        unsafe { dealloc(ptr, layout) };
    }

    #[test]
    fn test_composite_allocator_basic() {
        let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
        let heap_addr = heap_ptr as usize;

        let mut allocator = CompositePageAllocator::<TEST_PAGE_SIZE>::new();
        allocator.init(heap_addr, TEST_HEAP_SIZE);

        let addr1 = allocator.alloc_pages(1, TEST_PAGE_SIZE).unwrap();
        let addr2 = allocator.alloc_pages(4, TEST_PAGE_SIZE).unwrap();

        assert!(addr1 >= heap_addr && addr1 < heap_addr + TEST_HEAP_SIZE);
        assert!(addr2 >= heap_addr && addr2 < heap_addr + TEST_HEAP_SIZE);

        allocator.dealloc_pages(addr1, 1);
        allocator.dealloc_pages(addr2, 4);

        dealloc_test_heap(heap_ptr, heap_layout);
    }

    #[test]
    fn test_composite_allocator_alignment() {
        let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
        let heap_addr = heap_ptr as usize;

        let mut allocator = CompositePageAllocator::<TEST_PAGE_SIZE>::new();
        allocator.init(heap_addr, TEST_HEAP_SIZE);

        let addr = allocator.alloc_pages(1, TEST_PAGE_SIZE * 4).unwrap();
        assert_eq!(addr & (TEST_PAGE_SIZE * 4 - 1), 0);

        allocator.dealloc_pages(addr, 1);
        dealloc_test_heap(heap_ptr, heap_layout);
    }
}
