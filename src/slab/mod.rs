//! Slab allocator — bitmap-based with lock-free cross-CPU freeing.
//!
//! The [`SlabAllocator`] is a standalone component that manages object allocation
//! within pre-supplied slab pages.  It does **not** allocate pages itself; instead
//! it returns [`SlabAllocResult::NeedsSlab`] to request pages from the caller.
//!
//! Cross-CPU frees go through the lock-free [`SlabPageHeader::remote_free`] path.

pub mod cache;
pub mod page;
pub mod size_class;

pub use page::SlabPageHeader;
pub use size_class::SizeClass;

use cache::{CacheDeallocResult, SlabCache};
use core::alloc::Layout;
use core::ptr::NonNull;

use crate::error::{AllocError, AllocResult};

/// Result of a slab allocation attempt.
pub enum SlabAllocResult {
    /// Object successfully allocated.
    Allocated(NonNull<u8>),
    /// The slab cache for this size class has no free objects.
    /// The caller should allocate `pages` pages from the buddy allocator,
    /// call [`SlabAllocator::add_slab`], and retry.
    NeedsSlab { size_class: SizeClass, pages: usize },
}

/// Result of a slab deallocation.
pub enum SlabDeallocResult {
    /// Object freed, nothing else to do.
    Done,
    /// The slab page at `base` became empty and should be returned to the buddy.
    FreeSlab { base: usize, pages: usize },
}

/// Standalone slab allocator (one per CPU or standalone use).
pub struct SlabAllocator<const PAGE_SIZE: usize = 0x1000> {
    caches: [SlabCache; SizeClass::COUNT],
}

impl<const PAGE_SIZE: usize> SlabAllocator<PAGE_SIZE> {
    /// Create a new (empty) slab allocator.  No pages are owned yet.
    pub const fn new() -> Self {
        Self {
            caches: [
                SlabCache::new(SizeClass::Bytes8),
                SlabCache::new(SizeClass::Bytes16),
                SlabCache::new(SizeClass::Bytes32),
                SlabCache::new(SizeClass::Bytes64),
                SlabCache::new(SizeClass::Bytes128),
                SlabCache::new(SizeClass::Bytes256),
                SlabCache::new(SizeClass::Bytes512),
                SlabCache::new(SizeClass::Bytes1024),
                SlabCache::new(SizeClass::Bytes2048),
            ],
        }
    }

    /// Try to allocate an object matching `layout`.
    ///
    /// If the matching cache is exhausted, [`SlabAllocResult::NeedsSlab`] is returned
    /// so the caller can supply pages and retry.
    pub fn alloc(&mut self, layout: Layout) -> AllocResult<SlabAllocResult> {
        let sc = SizeClass::from_layout(layout).ok_or(AllocError::InvalidParam)?;
        let cache = &mut self.caches[sc.index()];

        match cache.alloc_object::<PAGE_SIZE>() {
            Some(addr) => {
                // SAFETY: `addr` is non-null, aligned, and within a live slab page.
                let ptr = unsafe { NonNull::new_unchecked(addr as *mut u8) };
                Ok(SlabAllocResult::Allocated(ptr))
            }
            None => Ok(SlabAllocResult::NeedsSlab {
                size_class: sc,
                pages: sc.slab_pages(PAGE_SIZE),
            }),
        }
    }

    /// Free an object previously allocated with [`alloc`](Self::alloc).
    ///
    /// This is the **local** (owner-CPU) path.  Cross-CPU frees should go through
    /// [`SlabPageHeader::remote_free`] directly (see [`GlobalAllocator`]).
    pub fn dealloc(&mut self, ptr: NonNull<u8>, layout: Layout) -> SlabDeallocResult {
        let sc = SizeClass::from_layout(layout).expect("layout exceeds slab size");
        let cache = &mut self.caches[sc.index()];

        match cache.dealloc_object::<PAGE_SIZE>(ptr.as_ptr() as usize) {
            CacheDeallocResult::Done => SlabDeallocResult::Done,
            CacheDeallocResult::FreeSlab { base, pages } => {
                SlabDeallocResult::FreeSlab { base, pages }
            }
        }
    }

    /// Supply a freshly allocated slab page to the given size class.
    ///
    /// `base` is the virtual address of the page(s), `bytes` = pages × PAGE_SIZE.
    pub fn add_slab(&mut self, size_class: SizeClass, base: usize, bytes: usize, owner_cpu: u16) {
        self.caches[size_class.index()].add_slab(base, bytes, owner_cpu);
    }
}
