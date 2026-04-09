/// Global allocator composing buddy (pages) + per-CPU slab (objects).
///
/// Implements [`core::alloc::GlobalAlloc`] so it can serve as `#[global_allocator]`.
/// Cross-CPU frees are lock-free via [`SlabPageHeader::remote_free`].
use core::alloc::{GlobalAlloc, Layout};
use core::ptr::{self, NonNull};
use core::sync::atomic::{AtomicBool, Ordering};

use spin::Mutex as SpinMutex;

use crate::buddy::{BuddyAllocator, PageFlags};
use crate::error::{AllocError, AllocResult};
use crate::slab::page::{SlabPageHeader, SLAB_MAGIC};
use crate::slab::size_class::{SizeClass, SLAB_MAX_SIZE};
use crate::slab::{SlabAllocResult, SlabAllocator, SlabDeallocResult};
use crate::{align_up, OsImpl};

struct RegionLayout {
    meta_start: usize,
    meta_size: usize,
    buddy_meta_size: usize,
    slab_offset: usize,
    managed_heap_start: usize,
    managed_heap_size: usize,
}

/// Unified allocator: buddy page allocator + per-CPU slab caches.
pub struct GlobalAllocator<const PAGE_SIZE: usize = 0x1000> {
    buddy: SpinMutex<BuddyAllocator<PAGE_SIZE>>,
    per_cpu_slabs: *mut SpinMutex<SlabAllocator<PAGE_SIZE>>,
    cpu_count: usize,
    os: Option<&'static dyn OsImpl>,
    initialized: AtomicBool,
}

// SAFETY: All mutable state is behind SpinMutex or AtomicBool.
// `per_cpu_slabs` is a raw pointer into the reserved metadata prefix of the
// caller-provided region (same lifetime model as BuddyAllocator::meta).
unsafe impl<const PAGE_SIZE: usize> Sync for GlobalAllocator<PAGE_SIZE> {}
unsafe impl<const PAGE_SIZE: usize> Send for GlobalAllocator<PAGE_SIZE> {}

impl<const PAGE_SIZE: usize> GlobalAllocator<PAGE_SIZE> {
    // ------------------------------------------------------------------
    // Metadata sizing
    // ------------------------------------------------------------------

    /// Required alignment for the reserved metadata prefix.
    const fn metadata_align() -> usize {
        let a1 = core::mem::align_of::<crate::buddy::PageMeta>();
        let a2 = core::mem::align_of::<SpinMutex<SlabAllocator<PAGE_SIZE>>>();
        if a1 > a2 {
            a1
        } else {
            a2
        }
    }

    fn metadata_layout_for_pages(pages: usize, cpu_count: usize) -> Option<(usize, usize, usize)> {
        let buddy_meta_size = pages.checked_mul(core::mem::size_of::<crate::buddy::PageMeta>())?;
        let slab_align = core::mem::align_of::<SpinMutex<SlabAllocator<PAGE_SIZE>>>();
        let slab_offset = align_up(buddy_meta_size, slab_align);
        let slab_size =
            core::mem::size_of::<SpinMutex<SlabAllocator<PAGE_SIZE>>>().checked_mul(cpu_count)?;
        let meta_size = slab_offset.checked_add(slab_size)?;
        Some((buddy_meta_size, slab_offset, meta_size))
    }

    fn available_heap_pages(
        region_end: usize,
        meta_start: usize,
        meta_size: usize,
    ) -> Option<usize> {
        let managed_heap_start = align_up(meta_start.checked_add(meta_size)?, PAGE_SIZE);
        if managed_heap_start > region_end {
            return Some(0);
        }
        Some((region_end - managed_heap_start) / PAGE_SIZE)
    }

    fn can_manage_pages(
        region_end: usize,
        meta_start: usize,
        cpu_count: usize,
        pages: usize,
    ) -> bool {
        let Some((_, _, meta_size)) = Self::metadata_layout_for_pages(pages, cpu_count) else {
            return false;
        };
        let Some(available_pages) = Self::available_heap_pages(region_end, meta_start, meta_size)
        else {
            return false;
        };
        available_pages >= pages
    }

    fn compute_region_layout(
        region_start: usize,
        region_size: usize,
        cpu_count: usize,
    ) -> Option<RegionLayout> {
        if cpu_count == 0 || region_size == 0 || !PAGE_SIZE.is_power_of_two() {
            return None;
        }

        let region_end = region_start.checked_add(region_size)?;
        let meta_start = align_up(region_start, Self::metadata_align());
        if meta_start >= region_end {
            return None;
        }

        let heap_search_start = align_up(region_start, PAGE_SIZE);
        let max_pages = if heap_search_start >= region_end {
            0
        } else {
            (region_end - heap_search_start) / PAGE_SIZE
        };

        let mut low = 0usize;
        let mut high = max_pages;
        while low < high {
            let mid = low + (high - low).div_ceil(2);
            if Self::can_manage_pages(region_end, meta_start, cpu_count, mid) {
                low = mid;
            } else {
                high = mid - 1;
            }
        }

        if low == 0 {
            return None;
        }

        let (buddy_meta_size, slab_offset, meta_size) =
            Self::metadata_layout_for_pages(low, cpu_count)?;
        let managed_heap_start = align_up(meta_start.checked_add(meta_size)?, PAGE_SIZE);
        let managed_heap_size = low.checked_mul(PAGE_SIZE)?;

        Some(RegionLayout {
            meta_start,
            meta_size,
            buddy_meta_size,
            slab_offset,
            managed_heap_start,
            managed_heap_size,
        })
    }

    // ------------------------------------------------------------------
    // Construction / initialisation
    // ------------------------------------------------------------------

    /// Create an uninitialised global allocator.
    pub const fn new() -> Self {
        Self {
            buddy: SpinMutex::new(BuddyAllocator::new()),
            per_cpu_slabs: ptr::null_mut(),
            cpu_count: 0,
            os: None,
            initialized: AtomicBool::new(false),
        }
    }
}

impl<const PAGE_SIZE: usize> Default for GlobalAllocator<PAGE_SIZE> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const PAGE_SIZE: usize> GlobalAllocator<PAGE_SIZE> {
    /// Initialise the allocator.
    ///
    /// # Arguments
    /// - `region` — total writable region to reserve for this allocator.
    ///   The allocator carves metadata from the region prefix and manages the remaining tail.
    /// - `cpu_count` — number of CPUs (≥ 1).
    /// - `os` — platform abstraction.
    ///
    /// # Safety
    /// - `region` must be writable and remain valid for the lifetime of this allocator.
    /// - Any bytes consumed by metadata or alignment padding become unavailable for allocation.
    pub unsafe fn init(
        &self,
        region: &mut [u8],
        cpu_count: usize,
        os: &'static dyn OsImpl,
    ) -> AllocResult {
        let region_start = region.as_mut_ptr() as usize;
        let region_size = region.len();
        let layout = Self::compute_region_layout(region_start, region_size, cpu_count)
            .ok_or(AllocError::InvalidParam)?;
        let meta_ptr = layout.meta_start as *mut u8;
        let slab_ptr = meta_ptr.add(layout.slab_offset) as *mut SpinMutex<SlabAllocator<PAGE_SIZE>>;

        // --- Init buddy ---
        let mut buddy = self.buddy.lock();
        buddy.init(
            meta_ptr,
            layout.buddy_meta_size,
            layout.managed_heap_start,
            layout.managed_heap_size,
            Some(os),
        )?;
        drop(buddy);

        // --- Init per-CPU slabs ---
        for i in 0..cpu_count {
            let slot = slab_ptr.add(i);
            slot.write(SpinMutex::new(SlabAllocator::new()));
        }

        // --- Write fields via interior mutability (self is &self for GlobalAlloc compat) ---
        let self_mut = self as *const Self as *mut Self;
        (*self_mut).per_cpu_slabs = slab_ptr;
        (*self_mut).cpu_count = cpu_count;
        (*self_mut).os = Some(os);
        self.initialized.store(true, Ordering::Release);

        log::debug!(
            "GlobalAllocator: {} CPUs, region {:#x}+{:#x}, meta {:#x}+{:#x}, managed heap {:#x}+{:#x}",
            cpu_count,
            region_start,
            region_size,
            layout.meta_start,
            layout.meta_size,
            layout.managed_heap_start,
            layout.managed_heap_size,
        );

        Ok(())
    }

    /// Start address of the heap range actually managed by the buddy allocator.
    pub fn managed_heap_start(&self) -> usize {
        self.buddy.lock().heap_start()
    }

    /// Size in bytes of the heap range actually managed by the buddy allocator.
    pub fn managed_heap_size(&self) -> usize {
        self.buddy.lock().heap_size()
    }

    // ------------------------------------------------------------------
    // Public page-level API (forwarded to buddy)
    // ------------------------------------------------------------------

    /// Allocate contiguous pages.  Returns the virtual start address.
    pub fn alloc_pages(&self, count: usize, align: usize) -> AllocResult<usize> {
        self.buddy.lock().alloc_pages(count, align)
    }

    /// Free pages previously obtained via [`alloc_pages`](Self::alloc_pages).
    pub fn dealloc_pages(&self, addr: usize, count: usize) {
        self.buddy.lock().dealloc_pages(addr, count);
    }

    /// Allocate pages with physical address below 4 GiB.
    pub fn alloc_pages_lowmem(&self, count: usize, align: usize) -> AllocResult<usize> {
        self.buddy.lock().alloc_pages_lowmem(count, align)
    }

    // ------------------------------------------------------------------
    // Object-level API (slab or buddy fallback)
    // ------------------------------------------------------------------

    /// Allocate memory for `layout`.  Returns a pointer on success.
    pub fn alloc(&self, layout: Layout) -> AllocResult<NonNull<u8>> {
        if !self.initialized.load(Ordering::Acquire) {
            return Err(AllocError::NotInitialized);
        }

        if self.is_slab_eligible(&layout) {
            self.slab_alloc(layout)
        } else {
            self.large_alloc(layout)
        }
    }

    /// Deallocate memory previously returned by [`alloc`](Self::alloc).
    ///
    /// # Safety
    /// `ptr` must have been returned by a prior `alloc` with the same `layout`.
    pub unsafe fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        if self.is_slab_eligible(&layout) {
            self.slab_dealloc(ptr, layout);
        } else {
            self.large_dealloc(ptr, layout);
        }
    }

    // ------------------------------------------------------------------
    // Internal: slab path
    // ------------------------------------------------------------------

    #[inline]
    fn is_slab_eligible(&self, layout: &Layout) -> bool {
        layout.size() <= SLAB_MAX_SIZE && layout.align() <= SLAB_MAX_SIZE
    }

    fn slab_alloc(&self, layout: Layout) -> AllocResult<NonNull<u8>> {
        let os = self.os.ok_or(AllocError::NotInitialized)?;
        let cpu = os.current_cpu_idx();
        debug_assert!(cpu < self.cpu_count);

        let slab_lock = unsafe { &*self.per_cpu_slabs.add(cpu) };
        let mut slab = slab_lock.lock();

        match slab.alloc(layout)? {
            SlabAllocResult::Allocated(ptr) => Ok(ptr),
            SlabAllocResult::NeedsSlab { size_class, pages } => {
                drop(slab); // release slab lock before locking buddy
                let bytes = pages * PAGE_SIZE;
                let addr = self.buddy.lock().alloc_pages(pages, bytes)?;
                // Tag the page as SLAB in buddy metadata.
                unsafe {
                    self.buddy.lock().set_page_flags(addr, PageFlags::Slab);
                }
                let mut slab = slab_lock.lock();
                slab.add_slab(size_class, addr, bytes, cpu as u16);
                match slab.alloc(layout)? {
                    SlabAllocResult::Allocated(ptr) => Ok(ptr),
                    SlabAllocResult::NeedsSlab { .. } => Err(AllocError::NoMemory),
                }
            }
        }
    }

    unsafe fn slab_dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        let os = self.os.expect("not initialized");
        let sc = SizeClass::from_layout(layout).expect("layout exceeds slab");
        let slab_bytes = sc.slab_pages(PAGE_SIZE) * PAGE_SIZE;
        let base =
            SlabPageHeader::base_from_obj_addr::<PAGE_SIZE>(ptr.as_ptr() as usize, slab_bytes);
        let hdr = &*(base as *const SlabPageHeader);
        debug_assert_eq!(hdr.magic, SLAB_MAGIC);

        let owner_cpu = hdr.owner_cpu as usize;
        let current_cpu = os.current_cpu_idx();

        if owner_cpu == current_cpu {
            // Local free path (under lock).
            let slab_lock = &*self.per_cpu_slabs.add(current_cpu);
            let mut slab = slab_lock.lock();
            match slab.dealloc(ptr, layout) {
                SlabDeallocResult::Done => {}
                SlabDeallocResult::FreeSlab { base, pages } => {
                    drop(slab);
                    self.buddy.lock().set_page_flags(base, PageFlags::Free);
                    self.buddy.lock().dealloc_pages(base, pages);
                }
            }
        } else {
            // Remote free path (lock-free CAS).
            hdr.remote_free(ptr.as_ptr() as usize);
        }
    }

    // ------------------------------------------------------------------
    // Internal: large allocation (buddy pages)
    // ------------------------------------------------------------------

    fn large_alloc(&self, layout: Layout) -> AllocResult<NonNull<u8>> {
        let pages = align_up(layout.size(), PAGE_SIZE) / PAGE_SIZE;
        let align = layout.align().max(PAGE_SIZE);
        let addr = self.buddy.lock().alloc_pages(pages, align)?;
        // SAFETY: buddy returns non-null, page-aligned addresses.
        Ok(unsafe { NonNull::new_unchecked(addr as *mut u8) })
    }

    unsafe fn large_dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        let pages = align_up(layout.size(), PAGE_SIZE) / PAGE_SIZE;
        self.buddy
            .lock()
            .dealloc_pages(ptr.as_ptr() as usize, pages);
    }
}

// ---------------------------------------------------------------------------
// GlobalAlloc implementation
// ---------------------------------------------------------------------------

unsafe impl<const PAGE_SIZE: usize> GlobalAlloc for GlobalAllocator<PAGE_SIZE> {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        match self.alloc(layout) {
            Ok(ptr) => ptr.as_ptr(),
            Err(_) => ptr::null_mut(),
        }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if let Some(nn) = NonNull::new(ptr) {
            self.dealloc(nn, layout);
        }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let new_layout = match Layout::from_size_align(new_size, layout.align()) {
            Ok(l) => l,
            Err(_) => return ptr::null_mut(),
        };

        let new_ptr = <Self as GlobalAlloc>::alloc(self, new_layout);
        if !new_ptr.is_null() {
            let copy_size = layout.size().min(new_size);
            ptr::copy_nonoverlapping(ptr, new_ptr, copy_size);
            <Self as GlobalAlloc>::dealloc(self, ptr, layout);
        }
        new_ptr
    }
}
