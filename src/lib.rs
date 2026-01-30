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
//! - **Optional Logging**: Conditional compilation with `log` feature
//! - **Memory Tracking**: Detailed statistics with `tracking` feature
//!
//! # Quick Start
//!
//! ```no_run
//! use buddy_slab_allocator::{GlobalAllocator, PageAllocator};
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

/// Default page size for backward compatibility (4KB)
pub const DEFAULT_PAGE_SIZE: usize = 0x1000;

/// The error type used for allocation operations.
///
/// # Examples
///
/// ```
/// use buddy_slab_allocator::AllocError;
///
/// fn handle_error(error: AllocError) {
///     match error {
///         AllocError::InvalidParam => eprintln!("Invalid parameters"),
///         AllocError::MemoryOverlap => eprintln!("Memory regions overlap"),
///         AllocError::NoMemory => eprintln!("Out of memory"),
///         AllocError::NotAllocated => eprintln!("Double free detected"),
///     }
/// }
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocError {
    /// Invalid `size` or alignment (e.g. unaligned)
    InvalidParam,
    /// Memory added by `add_memory` overlapped with existing memory
    MemoryOverlap,
    /// No enough memory to allocate
    NoMemory,
    /// Attempt to deallocate a memory region that was not allocated
    NotAllocated,
}

/// A [`Result`] type with [`AllocError`] as the error type.
pub type AllocResult<T = ()> = Result<T, AllocError>;

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

/// The base allocator trait inherited by other allocator traits.
///
/// Provides common initialization methods for all allocator types.
pub trait BaseAllocator {
    /// Initialize the allocator with a free memory region.
    ///
    /// # Arguments
    ///
    /// * `start` - Starting address of the memory region
    /// * `size` - Size of the memory region in bytes
    ///
    /// # Examples
    ///
    /// ```
    /// # use buddy_slab_allocator::BaseAllocator;
    /// # struct MyAllocator;
    /// # impl BaseAllocator for MyAllocator {
    /// #     fn init(&mut self, start: usize, size: usize) {}
    /// #     fn add_memory(&mut self, start: usize, size: usize) -> buddy_slab_allocator::AllocResult { Ok(()) }
    /// # }
    /// let mut alloc = MyAllocator;
    /// alloc.init(0x8000_0000, 16 * 1024 * 1024);
    /// ```
    fn init(&mut self, start: usize, size: usize);

    /// Add a free memory region to the allocator.
    ///
    /// # Arguments
    ///
    /// * `start` - Starting address of the memory region
    /// * `size` - Size of the memory region in bytes
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` on success, or an error if the region overlaps
    /// with existing memory.
    fn add_memory(&mut self, start: usize, size: usize) -> AllocResult;
}

/// Byte-granularity allocator for arbitrary-size allocations.
///
/// Provides methods for allocating and deallocating memory with
/// byte-level granularity.
pub trait ByteAllocator {
    /// Allocate memory with the given size (in bytes) and alignment.
    ///
    /// # Arguments
    ///
    /// * `layout` - Memory layout specifying size and alignment requirements
    ///
    /// # Returns
    ///
    /// Returns a pointer to the allocated memory on success, or an error
    /// if allocation fails.
    ///
    /// # Examples
    ///
    /// ```
    /// # use buddy_slab_allocator::ByteAllocator;
    /// # use core::alloc::Layout;
    /// # use core::ptr::NonNull;
    /// # struct MyAllocator;
    /// # impl ByteAllocator for MyAllocator {
    /// #     fn alloc(&mut self, layout: Layout) -> buddy_slab_allocator::AllocResult<NonNull<u8>> { Ok(NonNull::dangling()) }
    /// #     fn dealloc(&mut self, pos: NonNull<u8>, layout: Layout) {}
    /// #     fn total_bytes(&self) -> usize { 0 }
    /// #     fn used_bytes(&self) -> usize { 0 }
    /// #     fn available_bytes(&self) -> usize { 0 }
    /// # }
    /// let mut alloc = MyAllocator;
    /// let layout = Layout::from_size_align(64, 8).unwrap();
    /// let ptr = alloc.alloc(layout)?;
    /// # Ok::<(), buddy_slab_allocator::AllocError>(())
    /// ```
    fn alloc(&mut self, layout: Layout) -> AllocResult<NonNull<u8>>;

    /// Deallocate memory at the given position, size, and alignment.
    ///
    /// # Arguments
    ///
    /// * `pos` - Pointer to the memory to deallocate
    /// * `layout` - Memory layout specifying size and alignment requirements
    ///
    /// # Safety
    ///
    /// The pointer must have been previously allocated from this allocator
    /// with the same layout.
    fn dealloc(&mut self, pos: NonNull<u8>, layout: Layout);

    /// Returns total memory size in bytes managed by this allocator.
    fn total_bytes(&self) -> usize;

    /// Returns allocated memory size in bytes.
    fn used_bytes(&self) -> usize;

    /// Returns available memory size in bytes.
    fn available_bytes(&self) -> usize;
}

/// Page-granularity allocator for managing memory in pages.
///
/// Provides methods for allocating and deallocating contiguous pages
/// of memory with specific alignment requirements.
pub trait PageAllocator: BaseAllocator {
    /// The size of a memory page in bytes (must be a power of two).
    const PAGE_SIZE: usize;

    /// Allocate contiguous memory pages with given count and alignment (in bytes).
    ///
    /// # Arguments
    ///
    /// * `num_pages` - Number of pages to allocate
    /// * `alignment` - Alignment requirement in bytes (must be power of two)
    ///
    /// # Returns
    ///
    /// Returns the starting address of the allocated pages on success,
    /// or an error if allocation fails.
    ///
    /// # Examples
    ///
    /// ```
    /// # use buddy_slab_allocator::{PageAllocator, BaseAllocator};
    /// # struct MyAllocator;
    /// # impl BaseAllocator for MyAllocator {
    /// #     fn init(&mut self, start: usize, size: usize) {}
    /// #     fn add_memory(&mut self, start: usize, size: usize) -> buddy_slab_allocator::AllocResult { Ok(()) }
    /// # }
    /// # impl PageAllocator for MyAllocator {
    /// #     const PAGE_SIZE: usize = 0x1000;
    /// #     fn alloc_pages(&mut self, num_pages: usize, alignment: usize) -> buddy_slab_allocator::AllocResult<usize> { Ok(0) }
    /// #     fn dealloc_pages(&mut self, pos: usize, num_pages: usize) {}
    /// #     fn alloc_pages_at(&mut self, base: usize, num_pages: usize, alignment: usize) -> buddy_slab_allocator::AllocResult<usize> { Ok(0) }
    /// #     fn total_pages(&self) -> usize { 0 }
    /// #     fn used_pages(&self) -> usize { 0 }
    /// #     fn available_pages(&self) -> usize { 0 }
    /// # }
    /// let mut alloc = MyAllocator;
    /// let addr = alloc.alloc_pages(4, 0x1000)?;
    /// # Ok::<(), buddy_slab_allocator::AllocError>(())
    /// ```
    fn alloc_pages(&mut self, num_pages: usize, alignment: usize) -> AllocResult<usize>;

    /// Deallocate contiguous memory pages with given position and count.
    ///
    /// # Arguments
    ///
    /// * `pos` - Starting address of the pages to deallocate
    /// * `num_pages` - Number of pages to deallocate
    ///
    /// # Safety
    ///
    /// The address range must have been previously allocated from this allocator.
    fn dealloc_pages(&mut self, pos: usize, num_pages: usize);

    /// Allocate contiguous memory pages with given base address, count and alignment (in bytes).
    ///
    /// # Arguments
    ///
    /// * `base` - Desired starting address for allocation
    /// * `num_pages` - Number of pages to allocate
    /// * `alignment` - Alignment requirement in bytes (must be power of two)
    ///
    /// # Returns
    ///
    /// Returns the starting address of the allocated pages on success,
    /// or an error if the region cannot be allocated at the specified base.
    fn alloc_pages_at(
        &mut self,
        base: usize,
        num_pages: usize,
        alignment: usize,
    ) -> AllocResult<usize>;

    /// Returns the total number of memory pages managed by this allocator.
    fn total_pages(&self) -> usize;

    /// Returns the number of allocated memory pages.
    fn used_pages(&self) -> usize;

    /// Returns the number of available memory pages.
    fn available_pages(&self) -> usize;
}

/// ID allocator for managing unique identifiers (e.g., thread IDs).
///
/// Provides methods for allocating and deallocating unique IDs with
/// alignment constraints.
pub trait IdAllocator: BaseAllocator {
    /// Allocate contiguous IDs with given count and alignment.
    ///
    /// # Arguments
    ///
    /// * `count` - Number of IDs to allocate
    /// * `alignment` - Alignment requirement for the starting ID
    ///
    /// # Returns
    ///
    /// Returns the starting ID on success, or an error if allocation fails.
    fn alloc_id(&mut self, count: usize, alignment: usize) -> AllocResult<usize>;

    /// Deallocate contiguous IDs with given position and count.
    ///
    /// # Arguments
    ///
    /// * `start_id` - Starting ID of the range to deallocate
    /// * `count` - Number of IDs to deallocate
    ///
    /// # Safety
    ///
    /// The ID range must have been previously allocated from this allocator.
    fn dealloc_id(&mut self, start_id: usize, count: usize);

    /// Checks whether the given ID is currently allocated.
    fn is_allocated(&self, id: usize) -> bool;

    /// Mark the given ID as allocated and prevent it from being reallocated.
    ///
    /// # Arguments
    ///
    /// * `id` - The ID to mark as permanently allocated
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` on success, or an error if the ID is already allocated.
    fn alloc_fixed_id(&mut self, id: usize) -> AllocResult;

    /// Returns the maximum number of IDs supported by this allocator.
    fn size(&self) -> usize;

    /// Returns the number of currently allocated IDs.
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
