//! Buddy block metadata
//!
//! Represents a block of memory in the buddy system with order and address information.

use core::cmp::PartialOrd;

/// Maximum number of memory zones supported
pub const MAX_ZONES: usize = 10;

/// Maximum order supported
pub const DEFAULT_MAX_ORDER: usize = 28; // Support up to 256GB allocations (2^28 * 4KB)

/// Buddy block metadata
#[derive(Debug, Clone, Copy)]
pub struct BuddyBlock {
    pub order: usize,
    pub addr: usize,
}

impl BuddyBlock {
    /// Create a new buddy block
    pub const fn new(order: usize, addr: usize) -> Self {
        Self { order, addr }
    }

    /// Calculate the buddy address for this block
    /// The buddy is the other half of the parent block at the next higher order
    /// For a block at order k with address A, its buddy is at A ^ (2^k * PAGE_SIZE)
    #[allow(dead_code)]
    pub fn buddy_addr<const PAGE_SIZE: usize>(&self) -> usize {
        self.addr ^ ((1 << self.order) * PAGE_SIZE)
    }
}

impl PartialOrd for BuddyBlock {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        self.addr.partial_cmp(&other.addr)
    }
}

impl PartialEq for BuddyBlock {
    fn eq(&self, other: &Self) -> bool {
        self.addr == other.addr && self.order == other.order
    }
}

impl Eq for BuddyBlock {}

/// A memory zone descriptor (similar to Linux kernel's zone)
#[derive(Debug, Clone, Copy)]
pub struct ZoneInfo {
    pub start_addr: usize,
    pub end_addr: usize,
    pub total_pages: usize,
    pub zone_id: usize,
}
