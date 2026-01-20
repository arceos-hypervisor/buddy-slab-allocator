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
}

impl<const PAGE_SIZE: usize> BuddyPageAllocator<PAGE_SIZE> {
    pub const fn new() -> Self {
        Self {
            zones: [const { BuddySet::<PAGE_SIZE>::empty() }; MAX_ZONES],
            num_zones: 0,
            global_node_pool: GlobalNodePool::new(),
            #[cfg(feature = "tracking")]
            stats: BuddyStats::new(),
        }
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

        for i in 0..self.num_zones {
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
