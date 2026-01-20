//! Page allocator with contiguous block combination support.

use crate::buddy::{BuddyPageAllocator, DEFAULT_MAX_ORDER};
use crate::{AllocError, AllocResult, BaseAllocator, PageAllocator};

#[cfg(feature = "log")]
use log::{debug, warn};

/// Maximum number of buddy blocks in a single contiguous allocation
const MAX_PARTS_PER_ALLOC: usize = 8;

pub struct CompositePageAllocator<const PAGE_SIZE: usize = { crate::DEFAULT_PAGE_SIZE }> {
    /// Underlying buddy allocator for standard allocations
    buddy: BuddyPageAllocator<PAGE_SIZE>,
}

impl<const PAGE_SIZE: usize> CompositePageAllocator<PAGE_SIZE> {
    /// Create a new page allocator with contiguous block support
    pub const fn new() -> Self {
        Self {
            buddy: BuddyPageAllocator::<PAGE_SIZE>::new(),
        }
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

        // Check if we need to decompose the deallocation
        if num_pages.is_power_of_two() {
            // Power-of-2: can deallocate directly to buddy
            self.buddy.dealloc_pages(pos, num_pages);
        } else {
            self.buddy.dealloc_pages(pos, num_pages.next_power_of_two());
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
