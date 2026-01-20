//! Buddy page allocator module
//!
//! This module provides a complete buddy system implementation with:
//! - Sorted linked lists for efficient contiguity checking
//! - Multi-zone support
//! - Detailed statistics and debugging

pub mod buddy_allocator;
pub mod buddy_block;
pub mod buddy_set;
pub mod global_node_pool;
pub mod pooled_list;
pub mod stats;

pub use buddy_allocator::BuddyPageAllocator;
pub use buddy_block::{BuddyBlock, ZoneInfo, MAX_ZONES};
pub use buddy_set::BuddySet;
pub use global_node_pool::{GlobalNodePool, ListNode};
pub use pooled_list::PooledLinkedList;
#[cfg(not(feature = "tracking"))]
pub use stats::DEFAULT_MAX_ORDER;
#[cfg(feature = "tracking")]
pub use stats::{BuddyStats, DEFAULT_MAX_ORDER};
