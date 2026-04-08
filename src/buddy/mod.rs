//! Buddy page allocator — page-metadata-based with intrusive free lists.
//!
//! The allocator manages a contiguous virtual address range ("the heap").
//! An external metadata region stores one [`PageMeta`] per page frame,
//! enabling O(1) free-list operations without any dynamic allocation.

pub mod page_meta;

pub use page_meta::{PageFlags, PageMeta, PFN_NONE};

use crate::error::{AllocError, AllocResult};
use crate::{is_aligned, OsImpl};
use page_meta::{free_list_pop, free_list_push, free_list_remove};

/// Maximum buddy order.  With 4 KiB pages this gives 2^20 × 4 KiB = 4 GiB blocks.
pub const MAX_ORDER: usize = 20;

/// DMA32 zone upper bound (4 GiB physical).
const DMA32_LIMIT: usize = 0x1_0000_0000;

/// Page-metadata-based buddy allocator.
///
/// `PAGE_SIZE` must be a power of two (commonly 0x1000 = 4 KiB).
pub struct BuddyAllocator<const PAGE_SIZE: usize = 0x1000> {
    /// Pointer to the `PageMeta` array in the external metadata region.
    meta: *mut PageMeta,
    /// Maximum number of pages the metadata can describe.
    max_pages: usize,
    /// Virtual start address of the managed heap region.
    heap_start: usize,
    /// Size of the managed heap in bytes.
    heap_size: usize,
    /// Free-list head PFN per order (`PFN_NONE` = empty).
    free_lists: [u32; MAX_ORDER + 1],
    /// Number of currently free pages.
    free_pages: usize,
    /// Total number of pages in the heap.
    total_pages: usize,
    /// Optional OS interface for DMA32/lowmem address translation.
    os: Option<&'static dyn OsImpl>,
}

// SAFETY: The allocator is designed to be wrapped in a SpinMutex.
// Raw pointer field `meta` points to the externally supplied metadata region
// whose lifetime is managed by the caller.
unsafe impl<const PAGE_SIZE: usize> Send for BuddyAllocator<PAGE_SIZE> {}

impl<const PAGE_SIZE: usize> BuddyAllocator<PAGE_SIZE> {
    // ------------------------------------------------------------------
    // Construction helpers
    // ------------------------------------------------------------------

    /// Calculate the metadata-region size (in bytes) required for `heap_size` bytes.
    pub const fn required_meta_size(heap_size: usize) -> usize {
        let pages = heap_size / PAGE_SIZE;
        pages * core::mem::size_of::<PageMeta>()
    }

    /// Create an uninitialised allocator.  Call [`init`](Self::init) before use.
    pub const fn new() -> Self {
        Self {
            meta: core::ptr::null_mut(),
            max_pages: 0,
            heap_start: 0,
            heap_size: 0,
            free_lists: [PFN_NONE; MAX_ORDER + 1],
            free_pages: 0,
            total_pages: 0,
            os: None,
        }
    }

    /// Initialise the allocator over a heap region, using `meta` for page metadata.
    ///
    /// # Safety
    /// - `meta` must point to a writeable region of at least
    ///   [`required_meta_size`](Self::required_meta_size)`(heap_size)` bytes.
    /// - `heap_start` must be page-aligned and the region `[heap_start, heap_start + heap_size)`
    ///   must not overlap with the metadata region.
    /// - The caller is responsible for ensuring the metadata region lives as long as this allocator.
    pub unsafe fn init(
        &mut self,
        meta: *mut u8,
        meta_size: usize,
        heap_start: usize,
        heap_size: usize,
        os: Option<&'static dyn OsImpl>,
    ) -> AllocResult {
        // Validate
        if !PAGE_SIZE.is_power_of_two() {
            return Err(AllocError::InvalidParam);
        }
        if !is_aligned(heap_start, PAGE_SIZE) || heap_size == 0 {
            return Err(AllocError::InvalidParam);
        }
        let total_pages = heap_size / PAGE_SIZE;
        let required = Self::required_meta_size(heap_size);
        if meta_size < required {
            return Err(AllocError::InvalidParam);
        }

        let meta_ptr = meta as *mut PageMeta;

        // Zero-init all page metadata
        for i in 0..total_pages {
            meta_ptr.add(i).write(PageMeta::new());
        }

        self.meta = meta_ptr;
        self.max_pages = total_pages;
        self.heap_start = heap_start;
        self.heap_size = heap_size;
        self.free_lists = [PFN_NONE; MAX_ORDER + 1];
        self.free_pages = 0;
        self.total_pages = total_pages;
        self.os = os;

        // Build free lists: greedily carve the largest possible blocks.
        let mut pfn: usize = 0;
        while pfn < total_pages {
            // Find highest order block that (a) fits and (b) is naturally aligned.
            let mut order = MAX_ORDER;
            loop {
                let block_pages = 1usize << order;
                if block_pages <= total_pages - pfn && (pfn & (block_pages - 1)) == 0 {
                    break;
                }
                if order == 0 {
                    break;
                }
                order -= 1;
            }
            let block_pages = 1usize << order;
            let m = &mut *self.meta.add(pfn);
            m.flags = PageFlags::Free;
            m.order = order as u8;
            free_list_push(self.meta, &mut self.free_lists, pfn as u32, order);
            self.free_pages += block_pages;
            pfn += block_pages;
        }

        log::debug!(
            "BuddyAllocator: heap {:#x}..{:#x}, {} pages, {} free",
            heap_start,
            heap_start + heap_size,
            total_pages,
            self.free_pages,
        );

        Ok(())
    }

    // ------------------------------------------------------------------
    // Queries
    // ------------------------------------------------------------------

    /// Total number of pages managed.
    pub fn total_pages(&self) -> usize {
        self.total_pages
    }

    /// Number of currently free pages.
    pub fn free_pages(&self) -> usize {
        self.free_pages
    }

    /// Start address of the managed heap.
    pub fn heap_start(&self) -> usize {
        self.heap_start
    }

    /// Size of the managed heap in bytes.
    pub fn heap_size(&self) -> usize {
        self.heap_size
    }

    // ------------------------------------------------------------------
    // Allocation
    // ------------------------------------------------------------------

    /// Allocate `count` contiguous pages, returning the virtual address.
    ///
    /// `count` is rounded up to the nearest power of two.
    /// Optional `align` must be a power of two (in bytes) and ≥ `PAGE_SIZE`; 0 means
    /// default page alignment.
    pub fn alloc_pages(&mut self, count: usize, align: usize) -> AllocResult<usize> {
        if count == 0 {
            return Err(AllocError::InvalidParam);
        }
        let align = if align == 0 { PAGE_SIZE } else { align };
        if !align.is_power_of_two() || align < PAGE_SIZE {
            return Err(AllocError::InvalidParam);
        }

        let order = count.next_power_of_two().trailing_zeros() as usize;
        if order > MAX_ORDER {
            return Err(AllocError::InvalidParam);
        }

        // Alignment order: how many pages the alignment corresponds to.
        let align_order = (align / PAGE_SIZE).trailing_zeros() as usize;
        let effective_order = order.max(align_order);

        self.alloc_order(effective_order)
    }

    /// Low-level allocation by buddy order.
    fn alloc_order(&mut self, order: usize) -> AllocResult<usize> {
        // Search upwards for the first non-empty free list
        let mut found_order = order;
        while found_order <= MAX_ORDER {
            if self.free_lists[found_order] != PFN_NONE {
                break;
            }
            found_order += 1;
        }
        if found_order > MAX_ORDER {
            return Err(AllocError::NoMemory);
        }

        // Pop from found_order
        let pfn = unsafe { free_list_pop(self.meta, &mut self.free_lists, found_order) };
        debug_assert_ne!(pfn, PFN_NONE);

        // Split down to target order
        let mut current_order = found_order;
        while current_order > order {
            current_order -= 1;
            let buddy_pfn = pfn as usize + (1 << current_order);
            unsafe {
                let bm = &mut *self.meta.add(buddy_pfn);
                bm.flags = PageFlags::Free;
                bm.order = current_order as u8;
                free_list_push(
                    self.meta,
                    &mut self.free_lists,
                    buddy_pfn as u32,
                    current_order,
                );
            }
        }

        // Mark head page as allocated
        unsafe {
            let m = &mut *self.meta.add(pfn as usize);
            m.flags = PageFlags::Allocated;
            m.order = order as u8;
        }

        self.free_pages -= 1 << order;
        let addr = self.heap_start + (pfn as usize) * PAGE_SIZE;
        Ok(addr)
    }

    /// Allocate pages whose *physical* address is below 4 GiB (DMA32 zone).
    ///
    /// Requires [`OsImpl`] to have been set during init.
    pub fn alloc_pages_lowmem(&mut self, count: usize, align: usize) -> AllocResult<usize> {
        let os = self.os.ok_or(AllocError::InvalidParam)?;

        if count == 0 {
            return Err(AllocError::InvalidParam);
        }
        let align = if align == 0 { PAGE_SIZE } else { align };
        if !align.is_power_of_two() || align < PAGE_SIZE {
            return Err(AllocError::InvalidParam);
        }

        let order = count.next_power_of_two().trailing_zeros() as usize;
        let align_order = (align / PAGE_SIZE).trailing_zeros() as usize;
        let effective_order = order.max(align_order);
        if effective_order > MAX_ORDER {
            return Err(AllocError::InvalidParam);
        }

        // Walk free lists looking for a block below DMA32_LIMIT
        for search_order in effective_order..=MAX_ORDER {
            let mut pfn_u32 = self.free_lists[search_order];
            while pfn_u32 != PFN_NONE {
                let addr = self.heap_start + (pfn_u32 as usize) * PAGE_SIZE;
                let phys = os.virt_to_phys(addr);
                let block_bytes = (1usize << search_order) * PAGE_SIZE;
                if phys + block_bytes <= DMA32_LIMIT {
                    // Found! Remove from list, then split.
                    unsafe {
                        free_list_remove(self.meta, &mut self.free_lists, pfn_u32, search_order);
                    }

                    // Split
                    let mut current_order = search_order;
                    while current_order > effective_order {
                        current_order -= 1;
                        let buddy_pfn = pfn_u32 as usize + (1 << current_order);
                        unsafe {
                            let bm = &mut *self.meta.add(buddy_pfn);
                            bm.flags = PageFlags::Free;
                            bm.order = current_order as u8;
                            free_list_push(
                                self.meta,
                                &mut self.free_lists,
                                buddy_pfn as u32,
                                current_order,
                            );
                        }
                    }

                    unsafe {
                        let m = &mut *self.meta.add(pfn_u32 as usize);
                        m.flags = PageFlags::Allocated;
                        m.order = effective_order as u8;
                    }
                    self.free_pages -= 1 << effective_order;
                    return Ok(addr);
                }
                pfn_u32 = unsafe { (*self.meta.add(pfn_u32 as usize)).next };
            }
        }

        Err(AllocError::NoMemory)
    }

    // ------------------------------------------------------------------
    // Deallocation
    // ------------------------------------------------------------------

    /// Free pages previously obtained via [`alloc_pages`](Self::alloc_pages).
    ///
    /// `addr` must be the exact address returned by alloc, and `count` must match.
    pub fn dealloc_pages(&mut self, addr: usize, count: usize) {
        debug_assert!(is_aligned(addr, PAGE_SIZE));
        debug_assert!(addr >= self.heap_start);

        let pfn = (addr - self.heap_start) / PAGE_SIZE;
        debug_assert!(pfn < self.max_pages);

        let order = count.next_power_of_two().trailing_zeros() as usize;
        self.dealloc_order(pfn, order);
    }

    /// Mark the page at `pfn` with the given flags (used by slab to tag pages).
    ///
    /// # Safety
    /// The caller must ensure `pfn` is valid and properly allocated.
    pub unsafe fn set_page_flags(&mut self, addr: usize, flags: PageFlags) {
        let pfn = (addr - self.heap_start) / PAGE_SIZE;
        (*self.meta.add(pfn)).flags = flags;
    }

    /// Read the flags of the page containing `addr`.
    pub fn page_flags(&self, addr: usize) -> PageFlags {
        let pfn = (addr - self.heap_start) / PAGE_SIZE;
        unsafe { (*self.meta.add(pfn)).flags }
    }

    /// Internal: free a block at `pfn` of the given `order`, merging buddies.
    fn dealloc_order(&mut self, mut pfn: usize, mut order: usize) {
        // Only the originally freed block's pages are newly freed;
        // merged buddies were already counted as free.
        let freed_pages = 1usize << order;

        while order < MAX_ORDER {
            let buddy_pfn = pfn ^ (1 << order);
            if buddy_pfn >= self.max_pages {
                break;
            }
            let buddy = unsafe { &*self.meta.add(buddy_pfn) };
            if buddy.flags != PageFlags::Free || buddy.order as usize != order {
                break;
            }
            // Merge: remove buddy from its free list
            unsafe {
                free_list_remove(self.meta, &mut self.free_lists, buddy_pfn as u32, order);
            }
            pfn = pfn.min(buddy_pfn);
            order += 1;
        }

        unsafe {
            let m = &mut *self.meta.add(pfn);
            m.flags = PageFlags::Free;
            m.order = order as u8;
            free_list_push(self.meta, &mut self.free_lists, pfn as u32, order);
        }
        self.free_pages += freed_pages;
    }
}
