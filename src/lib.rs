//! Axvisor Memory Allocator
//!
//! This module implements a high-performance memory allocator for Axvisor hypervisor,
//! featuring:
//! - Buddy page allocator for page-level allocation
//! - Slab allocator for small object allocation
//! - Global allocator coordination
//! - Per-CPU caching support (future)

#![no_std]

extern crate alloc;

use core::alloc::Layout;
use core::ptr::NonNull;

// Logging support - conditionally import log crate
#[cfg(feature = "log")]
extern crate log;

// Stub macros when log is disabled - these become no-ops
#[cfg(not(feature = "log"))]
macro_rules! error {
    ($($arg:tt)*) => {};
}
#[cfg(not(feature = "log"))]
macro_rules! warn {
    ($($arg:tt)*) => {};
}
#[cfg(not(feature = "log"))]
macro_rules! info {
    ($($arg:tt)*) => {};
}
#[cfg(not(feature = "log"))]
macro_rules! debug {
    ($($arg:tt)*) => {};
}
#[cfg(not(feature = "log"))]
#[allow(unused_macros)]
macro_rules! trace {
    ($($arg:tt)*) => {};
}

/// Default page size for backward compatibility
pub const DEFAULT_PAGE_SIZE: usize = 0x1000;

/// The error type used for allocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocError {
    /// Invalid `size` or alignment. (e.g. unaligned)
    InvalidParam,
    /// Memory added by `add_memory` overlapped with existed memory.
    MemoryOverlap,
    /// No enough memory to allocate.
    NoMemory,
    /// Deallocate an unallocated memory region.
    NotAllocated,
}

/// A [`Result`] type with [`AllocError`] as the error type.
pub type AllocResult<T = ()> = Result<T, AllocError>;

/// Address translator used by allocators to reason about physical addresses.
///
/// Implementations should provide a stable virtual-to-physical mapping
/// for the allocator-managed address range.
pub trait AddrTranslator: Sync {
    /// Translate a virtual address to a physical address.
    ///
    /// Returns `None` if the address is not valid or not mapped.
    fn virt_to_phys(&self, va: usize) -> Option<usize>;
}

/// The base allocator inherited by other allocators.
pub trait BaseAllocator {
    /// Initialize the allocator with a free memory region.
    fn init(&mut self, start: usize, size: usize);

    /// Add a free memory region to the allocator.
    fn add_memory(&mut self, start: usize, size: usize) -> AllocResult;
}

/// Byte-granularity allocator.
pub trait ByteAllocator {
    /// Allocate memory with the given size (in bytes) and alignment.
    fn alloc(&mut self, layout: Layout) -> AllocResult<NonNull<u8>>;

    /// Deallocate memory at the given position, size, and alignment.
    fn dealloc(&mut self, pos: NonNull<u8>, layout: Layout);

    /// Returns total memory size in bytes.
    fn total_bytes(&self) -> usize;

    /// Returns allocated memory size in bytes.
    fn used_bytes(&self) -> usize;

    /// Returns available memory size in bytes.
    fn available_bytes(&self) -> usize;
}

/// Page-granularity allocator.
pub trait PageAllocator: BaseAllocator {
    /// The size of a memory page.
    const PAGE_SIZE: usize;

    /// Allocate contiguous memory pages with given count and alignment (in bytes).
    fn alloc_pages(&mut self, num_pages: usize, alignment: usize) -> AllocResult<usize>;

    /// Deallocate contiguous memory pages with given position and count.
    fn dealloc_pages(&mut self, pos: usize, num_pages: usize);

    /// Allocate contiguous memory pages with given base address, count and alignment (in bytes).
    fn alloc_pages_at(
        &mut self,
        base: usize,
        num_pages: usize,
        alignment: usize,
    ) -> AllocResult<usize>;

    /// Returns the total number of memory pages.
    fn total_pages(&self) -> usize;

    /// Returns the number of allocated memory pages.
    fn used_pages(&self) -> usize;

    /// Returns the number of available memory pages.
    fn available_pages(&self) -> usize;
}

/// Used to allocate unique IDs (e.g., thread ID).
pub trait IdAllocator: BaseAllocator {
    /// Allocate contiguous IDs with given count and alignment.
    fn alloc_id(&mut self, count: usize, alignment: usize) -> AllocResult<usize>;

    /// Deallocate contiguous IDs with given position and count.
    fn dealloc_id(&mut self, start_id: usize, count: usize);

    /// Whether the given `id` was allocated.
    fn is_allocated(&self, id: usize) -> bool;

    /// Mark the given `id` has been allocated and cannot be reallocated.
    fn alloc_fixed_id(&mut self, id: usize) -> AllocResult;

    /// Returns the maximum number of supported IDs.
    fn size(&self) -> usize;

    /// Returns the number of allocated IDs.
    fn used(&self) -> usize;

    /// Returns the number of available IDs.
    fn available(&self) -> usize;
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

#[cfg(doc)]
/// Documentation tests and examples
///
/// # Basic Usage
///
/// ```no_run
/// use buddy_slab_allocator::{GlobalAllocator, PageAllocator};
///
/// const PAGE_SIZE: usize = 0x1000;
/// let allocator = GlobalAllocator::<PAGE_SIZE>::new();
///
/// // Initialize with memory region
/// let heap_start = 0x8000_0000;
/// let heap_size = 16 * 1024 * 1024; // 16MB
/// allocator.init(heap_start, heap_size).unwrap();
///
/// // Allocate pages
/// let addr = allocator.alloc_pages(4, PAGE_SIZE).unwrap();
/// // Use the allocated memory...
/// allocator.dealloc_pages(addr, 4);
/// ```
///
/// # Small Object Allocation
///
/// ```no_run
/// use buddy_slab_allocator::GlobalAllocator;
/// use core::alloc::Layout;
///
/// const PAGE_SIZE: usize = 0x1000;
/// let allocator = GlobalAllocator::<PAGE_SIZE>::new();
/// allocator.init(0x8000_0000, 16 * 1024 * 1024).unwrap();
///
/// // Small allocations go through slab allocator
/// let layout = Layout::from_size_align(64, 8).unwrap();
/// let ptr = allocator.alloc(layout).unwrap();
/// // Use the allocated memory...
/// allocator.dealloc(ptr, layout);
/// ```
///
/// # Statistics Tracking
///
/// ```no_run
/// # #[cfg(feature = "tracking")]
/// # {
/// use buddy_slab_allocator::GlobalAllocator;
///
/// const PAGE_SIZE: usize = 0x1000;
/// let allocator = GlobalAllocator::<PAGE_SIZE>::new();
/// allocator.init(0x8000_0000, 16 * 1024 * 1024).unwrap();
///
/// let stats = allocator.get_stats();
/// println!("Total pages: {}", stats.total_pages);
/// println!("Used pages: {}", stats.used_pages);
/// println!("Free pages: {}", stats.free_pages);
/// # }
/// ```
pub mod _examples {}
