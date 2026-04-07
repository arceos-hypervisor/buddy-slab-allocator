//! buddy-slab-allocator Memory Allocator
//!
//! This crate implements a high-performance memory allocator designed for embedded
//! and kernel environments, featuring:
//! - Buddy page allocator for page-level allocation
//! - Slab allocator for small object allocation
//! - Global allocator coordination
//! - Zero `std` dependency (fully `#![no_std]`)
//!
//! # Features
//!
//! - **Buddy Page Allocator**: Efficient page-level memory allocation with automatic merging
//! - **Slab Byte Allocator**: Fast small object allocation (≤2048 bytes)
//! - **Global Allocator**: Automatic selection between page and slab allocation based on size
//! - **No_std Compatible**: Fully `#![no_std]` for embedded/kernel use
//! - **Logging Support**: Integrates with the `log` crate for allocation diagnostics
//! - **Memory Tracking**: Detailed statistics with `tracking` feature
//!
//! # Quick Start
//!
//! ```no_run
//! use buddy_slab_allocator::GlobalAllocator;
//! use core::alloc::Layout;
//!
//! const PAGE_SIZE: usize = 0x1000;
//! let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
//!
//! // Initialize with memory region
//! let heap_start = 0x8000_0000;
//! let heap_size = 16 * 1024 * 1024; // 16MB
//! allocator.init(heap_start, heap_size).unwrap();
//!
//! // Allocate pages
//! let addr = allocator.alloc_pages(4, PAGE_SIZE).unwrap();
//! // Use the allocated memory...
//! allocator.dealloc_pages(addr, 4);
//! ```
//!
//! # Small Object Allocation
//!
//! ```no_run
//! use buddy_slab_allocator::GlobalAllocator;
//! use core::alloc::Layout;
//!
//! const PAGE_SIZE: usize = 0x1000;
//! let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
//! allocator.init(0x8000_0000, 16 * 1024 * 1024).unwrap();
//!
//! // Small allocations go through slab allocator
//! let layout = Layout::from_size_align(64, 8).unwrap();
//! let ptr = allocator.alloc(layout).unwrap();
//! // Use the allocated memory...
//! allocator.dealloc(ptr, layout);
//! ```
//!
//! # Statistics Tracking
//!
//! ```no_run
//! # #[cfg(feature = "tracking")]
//! # {
//! use buddy_slab_allocator::GlobalAllocator;
//!
//! const PAGE_SIZE: usize = 0x1000;
//! let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
//! allocator.init(0x8000_0000, 16 * 1024 * 1024).unwrap();
//!
//! let stats = allocator.get_stats();
//! println!("Total pages: {}", stats.total_pages);
//! println!("Used pages: {}", stats.used_pages);
//! println!("Free pages: {}", stats.free_pages);
//! # }
//! ```

#![no_std]

extern crate alloc;

mod error;
pub use error::{AllocError, AllocResult};

/// Default page size for backward compatibility (4KB)
pub const DEFAULT_PAGE_SIZE: usize = 0x1000;

/// Address translator used by allocators to reason about physical addresses.
///
/// Implementations should provide a stable virtual-to-physical mapping
/// for the allocator-managed address range.
///
/// # Examples
///
/// ```
/// use buddy_slab_allocator::AddrTranslator;
///
/// struct SimpleMapper;
///
/// impl AddrTranslator for SimpleMapper {
///     fn virt_to_phys(&self, va: usize) -> Option<usize> {
///         // Identity mapping for this example
///         Some(va)
///     }
/// }
/// ```
pub trait AddrTranslator: Sync {
    /// Translate a virtual address to a physical address.
    ///
    /// Returns `None` if the address is not valid or not mapped.
    fn virt_to_phys(&self, va: usize) -> Option<usize>;
}

#[inline]
#[allow(dead_code)]
const fn align_down(pos: usize, align: usize) -> usize {
    pos & !(align - 1)
}

#[inline]
#[allow(dead_code)]
const fn align_up(pos: usize, align: usize) -> usize {
    (pos + align - 1) & !(align - 1)
}

/// Checks whether the address has the demanded alignment.
///
/// Equivalent to `addr % align == 0`, but the alignment must be a power of two.
#[inline]
#[allow(dead_code)]
const fn is_aligned(base_addr: usize, align: usize) -> bool {
    base_addr & (align - 1) == 0
}

// Export our allocator implementations
pub mod buddy;
#[cfg(feature = "tracking")]
pub use buddy::BuddyStats;
pub use buddy::{BuddyPageAllocator, DEFAULT_MAX_ORDER, MAX_ZONES};

pub mod page_allocator;
pub use page_allocator::CompositePageAllocator;

pub mod slab;
pub use slab::slab_byte_allocator::{PageAllocatorForSlab, SizeClass, SlabByteAllocator};

pub mod global_allocator;
pub use global_allocator::GlobalAllocator;
#[cfg(feature = "tracking")]
pub use global_allocator::UsageStats;
