//! Single-zone buddy allocator using global node pool
//!
//! Implements the core buddy system for a single memory zone using
//! pooled linked lists that draw nodes from a shared global pool.

use crate::{AllocError, AllocResult};

#[cfg(feature = "log")]
use log::{error, warn};

use super::{
    buddy_block::{BuddyBlock, ZoneInfo, DEFAULT_MAX_ORDER},
    global_node_pool::GlobalNodePool,
    pooled_list::PooledLinkedList,
};

/// A buddy set implementation - represents a single zone
///
/// Uses pooled linked lists with global node pool for efficient memory usage.
/// All zones share the same global node pool.
pub struct BuddySet<const PAGE_SIZE: usize = { crate::DEFAULT_PAGE_SIZE }> {
    pub(crate) base_addr: usize,
    pub(crate) end_addr: usize,
    total_pages: usize,
    zone_id: usize,
    /// Free lists for each order
    free_lists: [PooledLinkedList; DEFAULT_MAX_ORDER + 1],
}

impl<const PAGE_SIZE: usize> BuddySet<PAGE_SIZE> {
    /// Create a new buddy set for a zone (uninitialized, must call init())
    pub const fn new(base_addr: usize, size: usize, zone_id: usize) -> Self {
        Self {
            base_addr,
            end_addr: base_addr + size,
            total_pages: size / PAGE_SIZE,
            zone_id,
            free_lists: [const { PooledLinkedList::new() }; DEFAULT_MAX_ORDER + 1],
        }
    }

    /// Create an empty buddy set
    pub const fn empty() -> Self {
        Self::new(0, 0, 0)
    }

    pub const fn max_order(&self) -> usize {
        DEFAULT_MAX_ORDER
    }

    /// Add a block to the appropriate list for its order
    fn add_block_to_order(
        &mut self,
        pool: &mut GlobalNodePool,
        order: usize,
        block: BuddyBlock,
    ) -> bool {
        if order > DEFAULT_MAX_ORDER {
            error!(
                "zone {}: Order {} exceeds maximum order {}",
                self.zone_id, order, DEFAULT_MAX_ORDER
            );
            return false;
        }

        self.free_lists[order].insert_sorted(pool, block)
    }

    /// Find a block with the given address in the free list for its order
    fn find_block_in_order(
        &self,
        pool: &GlobalNodePool,
        order: usize,
        addr: usize,
    ) -> Option<(usize, Option<usize>)> {
        if order > DEFAULT_MAX_ORDER {
            return None;
        }
        self.free_lists[order].find_by_addr(pool, addr)
    }

    /// Remove a block from its list
    #[allow(dead_code)]
    fn remove_block_from_order(
        &mut self,
        pool: &mut GlobalNodePool,
        order: usize,
        node_idx: usize,
    ) -> bool {
        if order > DEFAULT_MAX_ORDER {
            error!(
                "zone {}: Order {} exceeds maximum order {}",
                self.zone_id, order, DEFAULT_MAX_ORDER
            );
            return false;
        }
        self.free_lists[order].remove(pool, node_idx)
    }

    /// Check if an address belongs to this zone
    pub fn addr_in_zone(&self, addr: usize) -> bool {
        addr >= self.base_addr && addr < self.end_addr
    }

    /// Get zone information
    pub fn zone_info(&self) -> ZoneInfo {
        ZoneInfo {
            start_addr: self.base_addr,
            end_addr: self.end_addr,
            total_pages: self.total_pages,
            zone_id: self.zone_id,
        }
    }

    /// Initialize the buddy set with a memory region
    pub fn init(&mut self, pool: &mut GlobalNodePool, base_addr: usize, size: usize) {
        let aligned_base = base_addr & !(PAGE_SIZE - 1);
        let end = base_addr + size;
        let aligned_end = (end + PAGE_SIZE - 1) & !(PAGE_SIZE - 1);
        let aligned_size = aligned_end - aligned_base;

        if aligned_size == 0 || aligned_size < PAGE_SIZE {
            panic!("Aligned size is too small: {:#x}", aligned_size);
        }

        self.base_addr = aligned_base;
        self.end_addr = aligned_end;
        self.total_pages = aligned_size / PAGE_SIZE;

        // Reset free lists
        for list in &mut self.free_lists {
            list.clear(pool);
        }

        for pfn in 0..self.total_pages {
            let page_addr = self.base_addr + pfn * PAGE_SIZE;
            self.dealloc_pages(pool, page_addr, 1);
        }
    }

    /// Allocate pages using buddy system
    pub fn alloc_pages(
        &mut self,
        pool: &mut GlobalNodePool,
        num_pages: usize,
        alignment: usize,
    ) -> AllocResult<usize> {
        if num_pages == 0 {
            return Err(AllocError::InvalidParam);
        }

        // Find the required order (round up to next power of 2)
        let required_order = if num_pages.is_power_of_two() {
            num_pages.trailing_zeros() as usize
        } else {
            num_pages.next_power_of_two().trailing_zeros() as usize
        };

        if required_order > self.max_order() {
            error!(
                "required order: {}, max order: {}",
                required_order,
                self.max_order()
            );
            return Err(AllocError::NoMemory);
        }

        let align_pages = (alignment + PAGE_SIZE - 1) / PAGE_SIZE;
        let align_order = align_pages.trailing_zeros() as usize;
        let order_needed = required_order.max(align_order);

        // Try to find a block of the required order or higher
        for order in order_needed..=self.max_order() {
            if !self.free_lists[order].is_empty() {
                let mut block = self.free_lists[order].pop_front(pool).unwrap();

                // Split down to required order
                while block.order > order_needed {
                    block.order -= 1;
                    let split_size = (1 << block.order) * PAGE_SIZE;
                    let buddy_addr = block.addr + split_size;

                    // Push the second half back to free list (sorted!)
                    let success = self.add_block_to_order(
                        pool,
                        block.order,
                        BuddyBlock {
                            order: block.order,
                            addr: buddy_addr,
                        },
                    );
                    if !success {
                        warn!(
                            "Failed to push buddy block to free list during split at order {}",
                            block.order
                        );
                        // Put the original block back
                        self.add_block_to_order(pool, block.order + 1, block);
                        return Err(AllocError::NoMemory);
                    }
                }

                // Verify alignment requirement
                assert!(
                    block.addr % alignment == 0,
                    "Allocated address {:#x} is not aligned to {:#x} bytes ",
                    block.addr,
                    alignment
                );

                return Ok(block.addr);
            }
        }

        Err(AllocError::NoMemory)
    }

    /// Deallocate pages back to buddy system with automatic merging
    pub fn dealloc_pages(&mut self, pool: &mut GlobalNodePool, addr: usize, num_pages: usize) {
        if num_pages == 0 {
            warn!("zone {}: Trying to deallocate 0 pages", self.zone_id);
            return;
        }

        // Validate address belongs to this zone
        if !self.addr_in_zone(addr) {
            error!(
                "zone {}: Address {:#x} not in zone [{:#x}, {:#x})",
                self.zone_id, addr, self.base_addr, self.end_addr
            );
            return;
        }

        // Calculate order for this deallocation
        // Handle non-power-of-2 allocations by rounding up (same as alloc_pages)
        let mut order = if num_pages.is_power_of_two() {
            num_pages.trailing_zeros() as usize
        } else {
            num_pages.next_power_of_two().trailing_zeros() as usize
        };

        if order > DEFAULT_MAX_ORDER {
            error!(
                "zone {}: Order {} exceeds maximum supported order {}",
                self.zone_id, order, DEFAULT_MAX_ORDER
            );
            return;
        }

        // Convert address and pages to PFN (Page Frame Number)
        let pfn = addr / PAGE_SIZE;

        // Check alignment using PFN
        if pfn & ((1 << order) - 1) != 0 {
            error!(
                "zone {}: Page PFN {} is not properly aligned for order {} (needs alignment to {} pages)",
                self.zone_id, pfn, order, 1 << order
            );
            return;
        }

        // Check page alignment
        if addr & (PAGE_SIZE - 1) != 0 {
            error!(
                "zone {}: Attempt to free page at non-page-aligned address {:#x}",
                self.zone_id, addr
            );
            return;
        }

        // Integrated double-free detection and buddy merging
        let initial_order = order;
        let size = (1 << initial_order) * PAGE_SIZE;

        // 1. Descendant check: Check if any part of the block being freed is already free
        // This handles cases where a large block is freed but contains already free sub-blocks
        for i in 0..initial_order {
            if self.free_lists[i].has_block_in_range(pool, addr, addr + size) {
                warn!(
                    "zone {}: Double free (descendant) detected at order {} in range [{:#x}, {:#x})",
                    self.zone_id, i, addr, addr + size
                );
                return;
            }
        }

        // 2. Ancestor check and Merging loop
        // We check from initial_order up to max_order.
        // For each i, we check if the current aligned base is in free_lists[i].
        let mut current_addr = addr;
        let mut merging = true;

        for i in initial_order..=self.max_order() {
            let block_size = (1 << i) * PAGE_SIZE;
            let current_base = current_addr & !(block_size - 1);

            // Double-free detection (Ancestor check): Check if this block or its parent is already free
            if self.find_block_in_order(pool, i, current_base).is_some() {
                warn!(
                    "zone {}: Double free detected at addr {:#x} (found at order {})",
                    self.zone_id, addr, i
                );
                return;
            }

            // Buddy merging
            if merging && i < self.max_order() {
                let buddy_addr = current_base ^ block_size;
                if self.addr_in_zone(buddy_addr) {
                    if let Some((node_idx, prev_idx)) =
                        self.find_block_in_order(pool, i, buddy_addr)
                    {
                        // Buddy found, remove it and continue merging at next order
                        self.free_lists[i].remove_with_prev(pool, node_idx, prev_idx);
                        current_addr = current_base & buddy_addr;
                        order = i + 1;
                        continue;
                    }
                }
                // No buddy found or out of zone, stop merging but continue checking for double frees
                merging = false;
            }
        }

        // Add the final merged block to the appropriate free list (sorted!)
        let final_addr = current_addr;
        let block = BuddyBlock {
            order,
            addr: final_addr,
        };

        if !self.add_block_to_order(pool, order, block) {
            error!(
                "zone {}: Failed to push block to free list: addr={:#x}, order={}",
                self.zone_id, final_addr, order
            );
        }
    }

    /// Get statistics for this zone
    #[cfg(feature = "tracking")]
    pub fn get_stats(&self) -> super::stats::BuddyStats {
        let mut stats = super::stats::BuddyStats::new();
        stats.total_pages = self.total_pages;

        for order in 0..=DEFAULT_MAX_ORDER {
            let block_count = self.free_lists[order].len();
            stats.free_pages_by_order[order] = block_count;
            stats.free_pages += block_count * (1 << order);
        }

        stats.used_pages = stats.total_pages.saturating_sub(stats.free_pages);
        stats
    }

    /// Get free blocks of a specific order as an iterator
    pub fn get_free_blocks_by_order<'a>(
        &'a self,
        pool: &'a GlobalNodePool,
        order: u32,
    ) -> super::pooled_list::PooledListIter<'a> {
        self.free_lists[order as usize].iter(pool)
    }

    /// Get the number of blocks in a specific order
    pub fn get_order_block_count(&self, order: usize) -> usize {
        if order <= DEFAULT_MAX_ORDER {
            self.free_lists[order].len()
        } else {
            0
        }
    }

    /// Allocate pages at a specific address
    ///
    /// This method allocates memory at a specific address. If the address range
    /// is completely free, it will be allocated. If part of a larger free block,
    /// the block will be split appropriately.
    pub fn alloc_pages_at(
        &mut self,
        pool: &mut GlobalNodePool,
        base: usize,
        num_pages: usize,
        alignment: usize,
    ) -> AllocResult<usize> {
        if num_pages == 0 {
            return Err(AllocError::InvalidParam);
        }

        // Check if address belongs to this zone
        if !self.addr_in_zone(base) {
            error!(
                "zone {}: Address {:#x} not in zone [{:#x}, {:#x})",
                self.zone_id, base, self.base_addr, self.end_addr
            );
            return Err(AllocError::InvalidParam);
        }

        // Check page alignment
        if base & (PAGE_SIZE - 1) != 0 {
            error!(
                "zone {}: Address {:#x} is not page-aligned",
                self.zone_id, base
            );
            return Err(AllocError::InvalidParam);
        }

        // Check alignment requirement
        if base % alignment != 0 {
            error!(
                "zone {}: Address {:#x} is not aligned to {:#x}",
                self.zone_id, base, alignment
            );
            return Err(AllocError::InvalidParam);
        }

        // Check if range fits in zone
        let size = num_pages * PAGE_SIZE;
        if base + size > self.end_addr {
            error!(
                "zone {}: Allocation range [{:#x}, {:#x}) exceeds zone end {:#x}",
                self.zone_id,
                base,
                base + size,
                self.end_addr
            );
            return Err(AllocError::InvalidParam);
        }

        // Calculate required order (round up to next power of 2 if needed)
        let required_order = if num_pages.is_power_of_two() {
            num_pages.trailing_zeros() as usize
        } else {
            num_pages.next_power_of_two().trailing_zeros() as usize
        };

        // Calculate the order for the block that contains this address
        // The block must be aligned to its size
        let pfn = base / PAGE_SIZE;
        let aligned_pfn = pfn & !((1 << required_order) - 1);

        // Check if the requested base is properly aligned for its size
        if aligned_pfn != pfn {
            error!(
                "zone {}: Base address {:#x} (PFN {}) is not aligned for {} pages",
                self.zone_id,
                base,
                pfn,
                1 << required_order
            );
            return Err(AllocError::InvalidParam);
        }

        // Try to find a free block that contains this address
        // Start from the required order and go up to larger blocks
        for order in required_order..=self.max_order() {
            let block_pfn = pfn & !((1 << order) - 1);
            let block_addr = block_pfn * PAGE_SIZE;

            // Check if this order can contain the request
            if let Some((node_idx, prev_idx)) = self.find_block_in_order(pool, order, block_addr) {
                // Verify the block is indeed in the free list and capture its data
                let node_data = {
                    let node = pool.get_node(node_idx).unwrap();
                    if node.data.order != order || node.data.addr != block_addr {
                        continue;
                    }
                    node.data
                };

                // Remove this block from free list using prev_idx for O(1) deletion
                self.free_lists[order].remove_with_prev(pool, node_idx, prev_idx);

                // Now we have a larger block, need to split it
                // to keep only the part that covers [base, base + size)
                let mut current_block = BuddyBlock {
                    order,
                    addr: block_addr,
                };

                // Split down to required order, keeping the requested region
                while current_block.order > required_order {
                    current_block.order -= 1;
                    let split_size = (1 << current_block.order) * PAGE_SIZE;

                    // Calculate buddy address
                    let buddy_addr = current_block.addr + split_size;

                    // Check if buddy is part of the requested region
                    let request_end = base + size;

                    if buddy_addr < base || buddy_addr >= request_end {
                        // Buddy is outside the requested region, add it back to free list
                        let success = self.add_block_to_order(
                            pool,
                            current_block.order,
                            BuddyBlock {
                                order: current_block.order,
                                addr: buddy_addr,
                            },
                        );
                        if !success {
                            error!(
                                "zone {}: Failed to return buddy block during split",
                                self.zone_id
                            );
                            // Put the original block back and fail
                            self.add_block_to_order(pool, order, node_data);
                            return Err(AllocError::NoMemory);
                        }
                    }
                    // If buddy is inside the requested region, keep it (don't add back)
                }

                // Verify we ended up with the correct block
                assert!(
                    current_block.addr == base,
                    "zone {}: Final block address {:#x} doesn't match requested {:#x}",
                    self.zone_id,
                    current_block.addr,
                    base
                );
                assert!(
                    current_block.order == required_order,
                    "zone {}: Final block order {} doesn't match required {}",
                    self.zone_id,
                    current_block.order,
                    required_order
                );

                return Ok(base);
            }
        }

        // No free block found that contains the requested address
        error!(
            "zone {}: No free block found for address {:#x} ({} pages)",
            self.zone_id, base, num_pages
        );
        Err(AllocError::NoMemory)
    }
}

impl Default for BuddySet {
    fn default() -> Self {
        Self::empty()
    }
}
