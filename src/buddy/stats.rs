//! Statistics and debugging for buddy allocator
//!
//! Provides detailed statistics tracking and failure reporting.

use super::buddy_block::ZoneInfo;

/// Maximum order supported
pub const DEFAULT_MAX_ORDER: usize = 28;

/// Buddy system statistics
#[derive(Debug, Clone, Copy)]
pub struct BuddyStats {
    pub total_pages: usize,
    pub free_pages: usize,
    pub used_pages: usize,
    pub free_pages_by_order: [usize; DEFAULT_MAX_ORDER + 1],
}

impl Default for BuddyStats {
    fn default() -> Self {
        Self {
            total_pages: 0,
            free_pages: 0,
            used_pages: 0,
            free_pages_by_order: [0; DEFAULT_MAX_ORDER + 1],
        }
    }
}

impl BuddyStats {
    pub const fn new() -> Self {
        Self {
            total_pages: 0,
            free_pages: 0,
            used_pages: 0,
            free_pages_by_order: [0; DEFAULT_MAX_ORDER + 1],
        }
    }

    /// Add statistics from another BuddyStats
    pub fn add(&mut self, other: &BuddyStats) {
        self.total_pages += other.total_pages;
        self.free_pages += other.free_pages;
        self.used_pages += other.used_pages;
        for (i, &count) in other.free_pages_by_order.iter().enumerate() {
            self.free_pages_by_order[i] += count;
        }
    }
}

/// Detailed memory statistics reporter
pub struct MemoryStatsReporter;

impl MemoryStatsReporter {
    /// Print detailed allocation failure statistics
    /// This is a standalone function to keep allocation logic clean
    #[allow(unused_variables)]
    pub fn print_alloc_failure_stats(
        page_size: usize,
        num_zones: usize,
        total_stats: &BuddyStats,
        zone_infos: &[ZoneInfo],
        zone_stats: &[BuddyStats],
        request_pages: usize,
        request_align: usize,
    ) {
        {
            #[cfg(feature = "log")]
            use log::error;
            error!("========================================");
            error!(
                "Request: {} pages ({} KB, alignment:{})",
                request_pages,
                (request_pages * page_size) / (1024),
                request_align
            );

            error!("Overall Memory State:");
            error!("  Total zones: {}", num_zones);
            error!(
                "  Total pages: {} ({} KB)",
                total_stats.total_pages,
                (total_stats.total_pages * page_size) / 1024
            );
            error!(
                "  Free pages: {} ({} KB)",
                total_stats.free_pages,
                (total_stats.free_pages * page_size) / (1024)
            );
            error!(
                "  Used pages: {} ({} KB)",
                total_stats.used_pages,
                (total_stats.used_pages * page_size) / (1024)
            );
            error!("========================================");

            for i in 0..num_zones {
                error!("Zone {}:", i);
                error!(
                    "  Range: [{:#x}, {:#x})",
                    zone_infos[i].start_addr, zone_infos[i].end_addr
                );
                error!("  Total pages: {}", zone_infos[i].total_pages);
                error!(
                    "  Free pages: {} / {}",
                    zone_stats[i].free_pages, zone_infos[i].total_pages
                );
                error!("  Free blocks by order:");

                for order in (0..=DEFAULT_MAX_ORDER).rev() {
                    let count = zone_stats[i].free_pages_by_order[order];
                    if count > 0 {
                        let block_size = (1 << order) * page_size;
                        let total_kb = (count * block_size) / (1024);
                        error!(
                            "    Order {}: {} blocks ({} KB each, {} KB total)",
                            order,
                            count,
                            block_size / (1024),
                            total_kb
                        );
                    }
                }
                error!("----------------------------------------");
            }

            error!("========================================");
        }
    }
}
