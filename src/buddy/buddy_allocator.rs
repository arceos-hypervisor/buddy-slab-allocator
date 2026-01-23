//! Multi-zone buddy allocator using global node pool
//!
//! Provides buddy allocator with support for multiple memory zones and
//! a single shared global node pool for all zones and orders.

use crate::{AllocError, AllocResult, BaseAllocator, PageAllocator};

#[cfg(feature = "log")]
use log::{debug, error, info, warn};

#[cfg(feature = "tracking")]
use super::ZoneInfo;

use super::{buddy_block::MAX_ZONES, buddy_set::BuddySet, global_node_pool::GlobalNodePool};

const NODE_POOL_PAGES: usize = 10;
const NODE_POOL_LOW_WATER_NODES: usize = 128;
const NODE_POOL_EXPAND_PAGES: usize = 5;
/// Threshold for low-memory (DMA32-like) physical addresses: 4GiB.
const LOWMEM_PHYS_THRESHOLD: usize = 1usize << 32;

#[cfg(feature = "tracking")]
use super::stats::{BuddyStats, MemoryStatsReporter};

/// Buddy page allocator with multi-zone support and global node pool
///
/// The `global_node_pool` stores linked-list nodes (ListNode<BuddyBlock>),
/// which are used to construct the free lists in each BuddySet.
/// Memory pages themselves are tracked by BuddyBlock values, not by this pool.
pub struct BuddyPageAllocator<const PAGE_SIZE: usize = { crate::DEFAULT_PAGE_SIZE }> {
    zones: [BuddySet<PAGE_SIZE>; MAX_ZONES],
    num_zones: usize,
    global_node_pool: GlobalNodePool,
    #[cfg(feature = "tracking")]
    stats: BuddyStats,
    /// Optional address translator used to reason about physical addresses.
    addr_translator: Option<&'static dyn crate::AddrTranslator>,
}

impl<const PAGE_SIZE: usize> BuddyPageAllocator<PAGE_SIZE> {
    pub const fn new() -> Self {
        Self {
            zones: [const { BuddySet::<PAGE_SIZE>::empty() }; MAX_ZONES],
            num_zones: 0,
            global_node_pool: GlobalNodePool::new(),
            #[cfg(feature = "tracking")]
            stats: BuddyStats::new(),
            addr_translator: None,
        }
    }

    /// Set the address translator so that the allocator can reason about
    /// physical address ranges (e.g. low-memory regions below 4GiB).
    pub fn set_addr_translator(&mut self, translator: &'static dyn crate::AddrTranslator) {
        self.addr_translator = Some(translator);
    }

    /// Initialize the global node pool and bootstrap with initial memory region
    pub fn init(&mut self, base_addr: usize, size: usize) {
        self.bootstrap(base_addr, size);
    }

    /// Bootstrap allocator with initial memory region
    pub fn bootstrap(&mut self, base_addr: usize, size: usize) {
        if self.num_zones >= MAX_ZONES {
            panic!("Cannot bootstrap: maximum zones reached");
        }

        // Reserve a small region at the beginning for the global node pool
        let node_region_size = NODE_POOL_PAGES * PAGE_SIZE;
        if size <= node_region_size {
            panic!("Cannot bootstrap: region too small for node pool");
        }
        let node_region_start = base_addr;

        self.global_node_pool
            .init(node_region_start, node_region_size);

        let zone_base = base_addr + node_region_size;
        let zone_size = size - node_region_size;

        self.zones[0] = BuddySet::new(zone_base, zone_size, 0);
        self.zones[0].init(&mut self.global_node_pool, zone_base, zone_size);
        // Mark whether this zone contains any low (<4G) physical memory, if translator is set.
        if let Some(translator) = self.addr_translator {
            if let Some(pa_start) = translator.virt_to_phys(zone_base) {
                if pa_start < LOWMEM_PHYS_THRESHOLD {
                    self.zones[0].is_lowmem = true;
                }
            }
        }
        self.num_zones = 1;

        #[cfg(feature = "tracking")]
        self.update_stats();
    }

    #[cfg(feature = "tracking")]
    pub fn get_stats(&self) -> BuddyStats {
        self.stats
    }

    /// Get global node pool statistics
    pub fn get_node_pool_stats(&self) -> super::global_node_pool::GlobalPoolStats {
        self.global_node_pool.get_stats()
    }

    /// Get number of zones in the allocator
    pub fn get_zone_count(&self) -> usize {
        self.num_zones
    }

    /// Allocate contiguous low-memory pages (physical address < 4GiB).
    ///
    /// This API is intended for DMA32-like use cases. It only considers zones
    /// that are marked as `is_lowmem`, and after allocation it performs a
    /// strict physical boundary check to ensure that both the start and end
    /// physical addresses are below the 4GiB threshold.
    pub fn alloc_pages_lowmem(&mut self, num_pages: usize, alignment: usize) -> AllocResult<usize> {
        if num_pages == 0 {
            return Err(AllocError::InvalidParam);
        }

        let translator = self.addr_translator.ok_or(AllocError::InvalidParam)?;

        // Try to expand node pool if we are close to exhaustion
        self.maybe_expand_node_pool();

        let size_bytes = num_pages * PAGE_SIZE;

        for i in 0..self.num_zones {
            if !self.zones[i].is_lowmem {
                continue;
            }

            match self.zones[i].alloc_pages(&mut self.global_node_pool, num_pages, alignment) {
                Ok(addr) => {
                    let start_va = addr;
                    let end_va = addr + size_bytes - 1;

                    // Ensure both start and end physical addresses are below the
                    // low-memory threshold to avoid crossing the 4GiB boundary.
                    if let (Some(pa_start), Some(pa_end)) = (
                        translator.virt_to_phys(start_va),
                        translator.virt_to_phys(end_va),
                    ) {
                        if pa_start < LOWMEM_PHYS_THRESHOLD && pa_end < LOWMEM_PHYS_THRESHOLD {
                            #[cfg(feature = "tracking")]
                            self.update_stats();
                            return Ok(addr);
                        }
                    }

                    // Boundary check failed: roll back this allocation and
                    // continue searching for another suitable block.
                    self.zones[i].dealloc_pages(&mut self.global_node_pool, addr, num_pages);
                }
                Err(_) => {
                    continue;
                }
            }
        }

        info!(
            "buddy allocator: Low-memory allocation failure: {} Byte, align {}",
            num_pages * PAGE_SIZE,
            alignment
        );
        Err(AllocError::NoMemory)
    }

    /// Get free blocks of a specific order from a zone
    /// Returns None if zone doesn't exist
    pub fn get_free_blocks_by_order<'a>(
        &'a self,
        zone_id: usize,
        order: u32,
    ) -> Option<super::pooled_list::PooledListIter<'a>> {
        if zone_id >= self.num_zones {
            return None;
        }
        Some(self.zones[zone_id].get_free_blocks_by_order(&self.global_node_pool, order))
    }

    /// Update aggregated statistics from all zones
    #[cfg(feature = "tracking")]
    fn update_stats(&mut self) {
        let mut total_stats = BuddyStats::new();

        for i in 0..self.num_zones {
            let zone_stats = self.zones[i].get_stats();
            total_stats.add(&zone_stats);
        }

        self.stats = total_stats;
    }

    /// Ensure the global node pool has enough free nodes.
    ///
    /// When the number of free nodes falls below a low-water mark,
    /// try to reserve a few pages from any available zone and add them as a new node region.
    fn maybe_expand_node_pool(&mut self) {
        let free_nodes = self.global_node_pool.free_node_count();
        if free_nodes >= NODE_POOL_LOW_WATER_NODES {
            return;
        }
        if self.num_zones == 0 {
            error!("buddy allocator: no zones available to expand node pool");
            return;
        }

        let expand_pages = NODE_POOL_EXPAND_PAGES;
        let expand_size = expand_pages * PAGE_SIZE;

        // Try all zones to allocate memory for node pool expansion
        for i in 0..self.num_zones {
            match self.zones[i].alloc_pages(&mut self.global_node_pool, expand_pages, PAGE_SIZE) {
                Ok(addr) => {
                    debug!(
                        "buddy allocator: expanding node pool from zone {}: free_nodes={} region=[{:#x}, {:#x})",
                        i,
                        free_nodes,
                        addr,
                        addr + expand_size
                    );
                    self.global_node_pool.add_region(addr, expand_size);
                    return;
                }
                Err(_) => {
                    continue;
                }
            }
        }

        warn!(
            "buddy allocator: failed to expand node pool at low water: free_nodes={} tried {} zones",
            free_nodes,
            self.num_zones
        );
    }

    /// Add a new memory region as a new zone
    pub fn add_memory_region(&mut self, start: usize, size: usize) -> AllocResult<()> {
        if self.num_zones >= MAX_ZONES {
            error!(
                "buddy allocator: Cannot add region: maximum zones ({}) reached",
                MAX_ZONES
            );
            return Err(AllocError::NoMemory);
        }

        // Align to page boundaries
        let aligned_start = start & !(PAGE_SIZE - 1);
        let end = start + size;
        let aligned_end = (end + PAGE_SIZE - 1) & !(PAGE_SIZE - 1);
        let aligned_size = aligned_end - aligned_start;

        if aligned_size == 0 || aligned_size < PAGE_SIZE {
            warn!(
                "buddy allocator: Aligned size is too small: {:#x}, skipping region",
                aligned_size
            );
            return Err(AllocError::InvalidParam);
        }

        // Check for overlap with existing zones
        for i in 0..self.num_zones {
            let zone = &self.zones[i];
            if !(aligned_end <= zone.base_addr || aligned_start >= zone.end_addr) {
                error!(
                    "buddy allocator: Region [{:#x}, {:#x}) overlaps with zone {} [{:#x}, {:#x})",
                    aligned_start, aligned_end, i, zone.base_addr, zone.end_addr
                );
                return Err(AllocError::MemoryOverlap);
            }
        }

        let zone_id = self.num_zones;
        self.zones[zone_id] = BuddySet::new(aligned_start, aligned_size, zone_id);
        self.zones[zone_id].init(&mut self.global_node_pool, aligned_start, aligned_size);
        // Mark whether this zone contains any low (<4G) physical memory, if translator is set.
        if let Some(translator) = self.addr_translator {
            if let Some(pa_start) = translator.virt_to_phys(aligned_start) {
                if pa_start < LOWMEM_PHYS_THRESHOLD {
                    self.zones[zone_id].is_lowmem = true;
                }
            }
        }
        self.num_zones += 1;

        // Print all zone information after successfully adding a new memory region
        #[cfg(feature = "tracking")]
        self.print_zone_info();

        Ok(())
    }

    /// Find the zone that contains the given address
    pub fn find_zone_for_addr(&self, addr: usize) -> Option<usize> {
        for i in 0..self.num_zones {
            if self.zones[i].addr_in_zone(addr) {
                return Some(i);
            }
        }
        None
    }

    /// Print detailed allocation failure statistics
    ///
    /// This method is public to allow CompositePageAllocator to call it
    /// when allocation fails, providing detailed per-zone failure information.
    #[cfg(feature = "tracking")]
    pub fn print_alloc_failure_stats(&self, num_pages: usize, alignment: usize) {
        let mut zone_infos: [Option<ZoneInfo>; MAX_ZONES] = [None; MAX_ZONES];
        let mut zone_stats: [Option<BuddyStats>; MAX_ZONES] = [None; MAX_ZONES];

        for i in 0..self.num_zones {
            zone_infos[i] = Some(self.zones[i].zone_info());
            zone_stats[i] = Some(self.zones[i].get_stats());
        }

        // Create slices from the initialized elements
        let zone_infos_slice: &[ZoneInfo] = unsafe {
            core::slice::from_raw_parts(zone_infos.as_ptr() as *const ZoneInfo, self.num_zones)
        };
        let zone_stats_slice: &[BuddyStats] = unsafe {
            core::slice::from_raw_parts(zone_stats.as_ptr() as *const BuddyStats, self.num_zones)
        };

        MemoryStatsReporter::print_alloc_failure_stats(
            PAGE_SIZE,
            self.num_zones,
            &self.stats,
            zone_infos_slice,
            zone_stats_slice,
            num_pages,
            alignment,
        );
    }

    /// Print all zone information and block distribution
    pub fn print_zone_info(&self) {
        info!("========== Buddy Allocator Zones Info ==========");
        info!("Total zones: {}", self.num_zones);
        info!("Page size: {:#x} ({})", PAGE_SIZE, PAGE_SIZE);
        info!("");

        for i in 0..self.num_zones {
            let zone = &self.zones[i];
            let _zone_info = zone.zone_info();
            info!("Zone {}:", i);
            info!(
                "  Address range: [{:#x}, {:#x})",
                _zone_info.start_addr, _zone_info.end_addr
            );
            info!("  Total pages: {}", _zone_info.total_pages);
            info!(
                "  Total size: {:#x} ({} MB)",
                _zone_info.total_pages * PAGE_SIZE,
                (_zone_info.total_pages * PAGE_SIZE) / (1024 * 1024)
            );
            info!("  Free blocks distribution:");

            // Print block distribution for each order
            for order in 0..=zone.max_order() {
                let block_count = zone.get_order_block_count(order);
                if block_count > 0 {
                    let _block_size = (1 << order) * PAGE_SIZE;
                    info!(
                        "    Order {}: {} blocks (size {} bytes each, total {:#x})",
                        order,
                        block_count,
                        _block_size,
                        block_count * _block_size
                    );
                }
            }
            info!("");
        }

        info!("Global node pool stats:");
        let _pool_stats = self.global_node_pool.get_stats();
        info!("  Total allocations: {}", _pool_stats.total_allocations);
        info!("  Free nodes: {}", _pool_stats.free_nodes);
        info!("==============================================");
    }

    #[cfg(not(feature = "tracking"))]
    pub fn print_alloc_failure_stats(&self, _num_pages: usize, _alignment: usize) {
        // No-op when tracking is disabled
    }
}

impl<const PAGE_SIZE: usize> crate::slab::PageAllocatorForSlab for BuddyPageAllocator<PAGE_SIZE> {
    fn alloc_pages(&mut self, num_pages: usize, alignment: usize) -> AllocResult<usize> {
        <Self as PageAllocator>::alloc_pages(self, num_pages, alignment)
    }

    fn dealloc_pages(&mut self, pos: usize, num_pages: usize) {
        <Self as PageAllocator>::dealloc_pages(self, pos, num_pages);
    }
}

impl<const PAGE_SIZE: usize> Default for BuddyPageAllocator<PAGE_SIZE> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const PAGE_SIZE: usize> BaseAllocator for BuddyPageAllocator<PAGE_SIZE> {
    fn init(&mut self, start: usize, size: usize) {
        self.bootstrap(start, size);
    }

    fn add_memory(&mut self, start: usize, size: usize) -> AllocResult<()> {
        self.add_memory_region(start, size)?;
        #[cfg(feature = "tracking")]
        self.update_stats();
        Ok(())
    }
}

impl<const PAGE_SIZE: usize> PageAllocator for BuddyPageAllocator<PAGE_SIZE> {
    const PAGE_SIZE: usize = PAGE_SIZE;

    fn alloc_pages(&mut self, num_pages: usize, alignment: usize) -> AllocResult<usize> {
        // Try to expand node pool if we are close to exhaustion
        self.maybe_expand_node_pool();

        // First, prefer zones that are NOT marked as low-memory so that
        // low-memory regions can be reserved for special use (e.g. DMA32).
        for i in 0..self.num_zones {
            if self.zones[i].is_lowmem {
                continue;
            }
            match self.zones[i].alloc_pages(&mut self.global_node_pool, num_pages, alignment) {
                Ok(addr) => {
                    #[cfg(feature = "tracking")]
                    self.update_stats();
                    return Ok(addr);
                }
                Err(_) => {
                    continue;
                }
            }
        }

        // Then, fall back to zones that are marked as low-memory.
        for i in 0..self.num_zones {
            if !self.zones[i].is_lowmem {
                continue;
            }
            match self.zones[i].alloc_pages(&mut self.global_node_pool, num_pages, alignment) {
                Ok(addr) => {
                    #[cfg(feature = "tracking")]
                    self.update_stats();
                    return Ok(addr);
                }
                Err(_) => {
                    continue;
                }
            }
        }

        debug!(
            "buddy allocator: Allocation failure: {} Byte, align {}",
            num_pages * PAGE_SIZE,
            alignment
        );
        Err(AllocError::NoMemory)
    }

    fn dealloc_pages(&mut self, pos: usize, num_pages: usize) {
        self.maybe_expand_node_pool();
        if let Some(zone_idx) = self.find_zone_for_addr(pos) {
            self.zones[zone_idx].dealloc_pages(&mut self.global_node_pool, pos, num_pages);
            #[cfg(feature = "tracking")]
            self.update_stats();
        } else {
            warn!(
                "buddy allocator: Dealloc pages at {:#x}: address not in any zone",
                pos
            );
        }
    }

    fn alloc_pages_at(
        &mut self,
        base: usize,
        num_pages: usize,
        alignment: usize,
    ) -> AllocResult<usize> {
        // Try to expand node pool if we are close to exhaustion
        self.maybe_expand_node_pool();

        if let Some(zone_idx) = self.find_zone_for_addr(base) {
            match self.zones[zone_idx].alloc_pages_at(
                &mut self.global_node_pool,
                base,
                num_pages,
                alignment,
            ) {
                Ok(addr) => {
                    #[cfg(feature = "tracking")]
                    self.update_stats();
                    Ok(addr)
                }
                Err(e) => Err(e),
            }
        } else {
            warn!(
                "buddy allocator: alloc_pages_at: address {:#x} not in any zone",
                base
            );
            Err(AllocError::InvalidParam)
        }
    }

    fn total_pages(&self) -> usize {
        #[cfg(feature = "tracking")]
        return self.stats.total_pages;
        #[cfg(not(feature = "tracking"))]
        return 0;
    }

    fn used_pages(&self) -> usize {
        #[cfg(feature = "tracking")]
        return self.stats.used_pages;
        #[cfg(not(feature = "tracking"))]
        return 0;
    }

    fn available_pages(&self) -> usize {
        #[cfg(feature = "tracking")]
        return self.stats.free_pages;
        #[cfg(not(feature = "tracking"))]
        return 0;
    }
}

#[cfg(test)]
mod tests {
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
    fn test_buddy_allocator_init() {
        let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
        let heap_addr = heap_ptr as usize;

        let mut allocator = BuddyPageAllocator::<TEST_PAGE_SIZE>::new();
        allocator.init(heap_addr, TEST_HEAP_SIZE);

        let addr = allocator.alloc_pages(1, TEST_PAGE_SIZE);
        assert!(addr.is_ok());
        if let Ok(a) = addr {
            allocator.dealloc_pages(a, 1);
        }

        dealloc_test_heap(heap_ptr, heap_layout);
    }

    #[test]
    fn test_buddy_allocator_multi_pages() {
        let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
        let heap_addr = heap_ptr as usize;

        let mut allocator = BuddyPageAllocator::<TEST_PAGE_SIZE>::new();
        allocator.init(heap_addr, TEST_HEAP_SIZE);

        let addr1 = allocator.alloc_pages(4, TEST_PAGE_SIZE).unwrap();
        let addr2 = allocator.alloc_pages(8, TEST_PAGE_SIZE).unwrap();
        assert_ne!(addr1, addr2);

        allocator.dealloc_pages(addr1, 4);
        allocator.dealloc_pages(addr2, 8);

        dealloc_test_heap(heap_ptr, heap_layout);
    }

    #[test]
    fn test_buddy_allocator_alignment() {
        let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
        let heap_addr = heap_ptr as usize;

        let mut allocator = BuddyPageAllocator::<TEST_PAGE_SIZE>::new();
        allocator.init(heap_addr, TEST_HEAP_SIZE);

        let addr = allocator.alloc_pages(1, TEST_PAGE_SIZE * 4).unwrap();
        assert_eq!(addr & (TEST_PAGE_SIZE * 4 - 1), 0);

        allocator.dealloc_pages(addr, 1);
        dealloc_test_heap(heap_ptr, heap_layout);
    }

    #[test]
    fn test_buddy_allocator_zone_count() {
        let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
        let heap_addr = heap_ptr as usize;

        let mut allocator = BuddyPageAllocator::<TEST_PAGE_SIZE>::new();
        allocator.init(heap_addr, TEST_HEAP_SIZE);

        assert_eq!(allocator.get_zone_count(), 1);

        dealloc_test_heap(heap_ptr, heap_layout);
    }
}
