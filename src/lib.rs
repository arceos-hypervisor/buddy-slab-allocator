//! # buddy-slab-allocator
//!
//! A `#![no_std]` memory allocator featuring:
//!
//! - **Buddy page allocator** — page-metadata-based with intrusive free lists
//! - **Slab allocator** — bitmap-based with lock-free cross-CPU freeing (Linux SLUB inspired)
//! - **Global allocator** — composes buddy + per-CPU slab, implements [`core::alloc::GlobalAlloc`]
//!
//! Both buddy and slab allocators can be used standalone.

#![no_std]

mod error;
pub use error::{AllocError, AllocResult};

pub mod buddy;
pub use buddy::BuddyAllocator;

pub mod slab;
pub use slab::{SizeClass, SlabAllocResult, SlabAllocator, SlabDeallocResult};

pub mod global;
pub use global::GlobalAllocator;

// ---------------------------------------------------------------------------
// OsImpl trait — the only interface the allocator needs from the OS / platform
// ---------------------------------------------------------------------------

/// Platform abstraction required by [`GlobalAllocator`].
///
/// Implementations must be safe to call from any CPU at any time.
pub trait OsImpl: Sync + Send {
    /// Return the index of the current CPU (0-based).
    fn current_cpu_idx(&self) -> usize;

    /// Translate a virtual address to a physical address.
    fn virt_to_phys(&self, vaddr: usize) -> usize;
}

// ---------------------------------------------------------------------------
// Utility helpers (crate-internal)
// ---------------------------------------------------------------------------

#[inline]
pub(crate) const fn align_up(pos: usize, align: usize) -> usize {
    (pos + align - 1) & !(align - 1)
}

#[inline]
pub(crate) const fn is_aligned(addr: usize, align: usize) -> bool {
    addr & (align - 1) == 0
}
