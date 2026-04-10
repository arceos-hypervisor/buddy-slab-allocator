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
#![feature(extern_item_impls)]

mod error;
pub use error::{AllocError, AllocResult};

pub mod buddy;
pub use buddy::{BuddyAllocator, ManagedSection};

pub mod slab;
pub use slab::{
    PerCpuSlab, SizeClass, SlabAllocResult, SlabAllocator, SlabDeallocResult, SlabTrait,
};

pub mod global;
pub use global::GlobalAllocator;

/// External interface items supplied by the platform / allocator integrator.
pub mod eii {
    /// Translate a virtual address to a physical address.
    #[eii(virt_to_phys_impl)]
    pub fn virt_to_phys(vaddr: usize) -> usize;

    /// Return the current CPU's slab object.
    #[eii(current_cpu_slab_impl)]
    pub fn current_cpu_slab() -> &'static dyn crate::SlabTrait;

    /// Return the owner slab for the given CPU.
    #[eii(remote_slab_impl)]
    pub fn remote_slab(cpu_idx: usize) -> &'static dyn crate::SlabTrait;
}

#[cfg(test)]
mod test_eii_impls {
    use core::{alloc::Layout, ptr::NonNull};

    use super::eii::{current_cpu_slab_impl, remote_slab_impl, virt_to_phys_impl};
    use super::{
        AllocError, AllocResult, SizeClass, SlabAllocResult, SlabDeallocResult, SlabTrait,
    };

    struct NullSlab;

    impl SlabTrait for NullSlab {
        fn cpu_id(&self) -> usize {
            0
        }

        fn alloc(&self, _layout: Layout) -> AllocResult<SlabAllocResult> {
            Err(AllocError::NotInitialized)
        }

        fn add_slab(&self, _size_class: SizeClass, _base: usize, _bytes: usize) {}

        fn dealloc_local(&self, _ptr: NonNull<u8>, _layout: Layout) -> SlabDeallocResult {
            SlabDeallocResult::Done
        }

        fn dealloc_remote(&self, _ptr: NonNull<u8>) {}
    }

    static NULL_SLAB: NullSlab = NullSlab;

    #[virt_to_phys_impl]
    fn test_virt_to_phys(vaddr: usize) -> usize {
        vaddr
    }

    #[current_cpu_slab_impl]
    fn test_current_cpu_slab() -> &'static dyn SlabTrait {
        &NULL_SLAB
    }

    #[remote_slab_impl]
    fn test_remote_slab(_cpu_idx: usize) -> &'static dyn SlabTrait {
        &NULL_SLAB
    }
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
