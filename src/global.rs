/// Global allocator composing buddy (pages) + per-CPU slab (objects).
///
/// Implements [`core::alloc::GlobalAlloc`] so it can serve as `#[global_allocator]`.
/// Cross-CPU frees are lock-free via [`SlabPageHeader::remote_free`].
use core::alloc::{GlobalAlloc, Layout};
use core::ptr::{self, NonNull};
use core::sync::atomic::{AtomicBool, Ordering};

use spin::Mutex as SpinMutex;

use crate::buddy::{BuddyAllocator, BuddySection, ManagedSection, PageFlags, SectionInitSpec};
use crate::error::{AllocError, AllocResult};
use crate::slab::page::{SLAB_MAGIC, SlabPageHeader};
use crate::slab::size_class::{SLAB_MAX_SIZE, SizeClass};
use crate::slab::{SlabAllocResult, SlabAllocator, SlabDeallocResult};
use crate::{OsImpl, align_up};

struct InitialRegionLayout {
    section_start: usize,
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
// caller-provided region.
unsafe impl<const PAGE_SIZE: usize> Sync for GlobalAllocator<PAGE_SIZE> {}
unsafe impl<const PAGE_SIZE: usize> Send for GlobalAllocator<PAGE_SIZE> {}

impl<const PAGE_SIZE: usize> GlobalAllocator<PAGE_SIZE> {
    const fn metadata_align() -> usize {
        let a1 = core::mem::align_of::<BuddySection>();
        let a2 = core::mem::align_of::<crate::buddy::PageMeta>();
        let a3 = core::mem::align_of::<SpinMutex<SlabAllocator<PAGE_SIZE>>>();
        let m = if a1 > a2 { a1 } else { a2 };
        if m > a3 { m } else { a3 }
    }

    fn metadata_layout_for_pages(pages: usize, cpu_count: usize) -> Option<(usize, usize, usize)> {
        let meta_offset = align_up(
            core::mem::size_of::<BuddySection>(),
            core::mem::align_of::<crate::buddy::PageMeta>(),
        );
        let buddy_meta_size = pages.checked_mul(core::mem::size_of::<crate::buddy::PageMeta>())?;
        let slab_align = core::mem::align_of::<SpinMutex<SlabAllocator<PAGE_SIZE>>>();
        let slab_offset = align_up(meta_offset.checked_add(buddy_meta_size)?, slab_align);
        let slab_size =
            core::mem::size_of::<SpinMutex<SlabAllocator<PAGE_SIZE>>>().checked_mul(cpu_count)?;
        let meta_size = slab_offset.checked_add(slab_size)?;
        Some((meta_offset, buddy_meta_size, meta_size))
    }

    fn available_heap_pages(
        region_end: usize,
        section_start: usize,
        meta_size: usize,
    ) -> Option<usize> {
        let managed_heap_start = align_up(section_start.checked_add(meta_size)?, PAGE_SIZE);
        if managed_heap_start > region_end {
            return Some(0);
        }
        Some((region_end - managed_heap_start) / PAGE_SIZE)
    }

    fn can_manage_pages(
        region_end: usize,
        section_start: usize,
        cpu_count: usize,
        pages: usize,
    ) -> bool {
        let Some((_, _, meta_size)) = Self::metadata_layout_for_pages(pages, cpu_count) else {
            return false;
        };
        let Some(available_pages) =
            Self::available_heap_pages(region_end, section_start, meta_size)
        else {
            return false;
        };
        available_pages >= pages
    }

    fn compute_initial_region_layout(
        region_start: usize,
        region_size: usize,
        cpu_count: usize,
    ) -> Option<InitialRegionLayout> {
        if cpu_count == 0 || region_size == 0 || !PAGE_SIZE.is_power_of_two() {
            return None;
        }

        let region_end = region_start.checked_add(region_size)?;
        let section_start = align_up(region_start, Self::metadata_align());
        if section_start >= region_end {
            return None;
        }

        let heap_search_start = align_up(
            section_start.checked_add(core::mem::size_of::<BuddySection>())?,
            PAGE_SIZE,
        );
        let max_pages = if heap_search_start >= region_end {
            0
        } else {
            (region_end - heap_search_start) / PAGE_SIZE
        };

        let mut low = 0usize;
        let mut high = max_pages;
        while low < high {
            let mid = low + (high - low).div_ceil(2);
            if Self::can_manage_pages(region_end, section_start, cpu_count, mid) {
                low = mid;
            } else {
                high = mid - 1;
            }
        }

        if low == 0 {
            return None;
        }

        let (meta_offset, buddy_meta_size, meta_size) =
            Self::metadata_layout_for_pages(low, cpu_count)?;
        let meta_start = section_start.checked_add(meta_offset)?;
        let slab_offset = align_up(
            meta_offset.checked_add(buddy_meta_size)?,
            core::mem::align_of::<SpinMutex<SlabAllocator<PAGE_SIZE>>>(),
        );
        let managed_heap_start = align_up(section_start.checked_add(meta_size)?, PAGE_SIZE);
        let managed_heap_size = low.checked_mul(PAGE_SIZE)?;

        Some(InitialRegionLayout {
            section_start,
            meta_start,
            meta_size,
            buddy_meta_size,
            slab_offset,
            managed_heap_start,
            managed_heap_size,
        })
    }

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
    /// Initialise the allocator over the first region.
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
        let layout = Self::compute_initial_region_layout(region_start, region_size, cpu_count)
            .ok_or(AllocError::InvalidParam)?;
        let section_ptr = layout.section_start as *mut BuddySection;
        let meta_ptr = layout.meta_start as *mut u8;
        let slab_ptr =
            (layout.section_start + layout.slab_offset) as *mut SpinMutex<SlabAllocator<PAGE_SIZE>>;

        let mut buddy = self.buddy.lock();
        buddy.reset(Some(os));
        buddy.add_region_raw(SectionInitSpec {
            region_start,
            region_size,
            section_ptr,
            meta_ptr,
            meta_size: layout.buddy_meta_size,
            heap_start: layout.managed_heap_start,
            heap_size: layout.managed_heap_size,
        })?;
        drop(buddy);

        for i in 0..cpu_count {
            let slot = slab_ptr.add(i);
            slot.write(SpinMutex::new(SlabAllocator::new()));
        }

        let self_mut = self as *const Self as *mut Self;
        (*self_mut).per_cpu_slabs = slab_ptr;
        (*self_mut).cpu_count = cpu_count;
        (*self_mut).os = Some(os);
        self.initialized.store(true, Ordering::Release);

        log::debug!(
            "GlobalAllocator: {} CPUs, region {:#x}+{:#x}, meta {:#x}+{:#x}, first heap {:#x}+{:#x}",
            cpu_count,
            region_start,
            region_size,
            layout.section_start,
            layout.meta_size,
            layout.managed_heap_start,
            layout.managed_heap_size,
        );

        Ok(())
    }

    /// Add a new managed region after [`init`](Self::init).
    ///
    /// # Safety
    /// - `region` must be writable and remain valid for the lifetime of this allocator.
    /// - The region must not overlap any already managed region.
    pub unsafe fn add_region(&self, region: &mut [u8]) -> AllocResult {
        if !self.initialized.load(Ordering::Acquire) {
            return Err(AllocError::NotInitialized);
        }
        self.buddy.lock().add_region(region)
    }

    /// Number of managed sections.
    pub fn managed_section_count(&self) -> usize {
        self.buddy.lock().section_count()
    }

    /// Read-only summary for a managed section.
    pub fn managed_section(&self, index: usize) -> Option<ManagedSection> {
        self.buddy.lock().section(index)
    }

    /// Total managed heap bytes across all sections.
    ///
    /// This excludes region-prefix metadata such as `BuddySection`, `PageMeta[]`,
    /// and per-CPU slab slots.
    pub fn managed_bytes(&self) -> usize {
        self.buddy.lock().managed_bytes()
    }

    /// Allocated backend bytes across all sections.
    ///
    /// This is page-level occupancy, not the exact sum of requested layout sizes.
    pub fn allocated_bytes(&self) -> usize {
        self.buddy.lock().allocated_bytes()
    }

    /// Allocate contiguous pages. Returns the virtual start address.
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

    /// Allocate memory for `layout`. Returns a pointer on success.
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
                drop(slab);
                let bytes = pages * PAGE_SIZE;
                let addr = self.buddy.lock().alloc_pages(pages, bytes)?;
                unsafe {
                    self.buddy.lock().set_page_flags(addr, PageFlags::Slab)?;
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
            let slab_lock = &*self.per_cpu_slabs.add(current_cpu);
            let mut slab = slab_lock.lock();
            match slab.dealloc(ptr, layout) {
                SlabDeallocResult::Done => {}
                SlabDeallocResult::FreeSlab { base, pages } => {
                    drop(slab);
                    self.buddy.lock().dealloc_pages(base, pages);
                }
            }
        } else {
            hdr.remote_free(ptr.as_ptr() as usize);
        }
    }

    fn large_alloc(&self, layout: Layout) -> AllocResult<NonNull<u8>> {
        let pages = align_up(layout.size(), PAGE_SIZE) / PAGE_SIZE;
        let align = layout.align().max(PAGE_SIZE);
        let addr = self.buddy.lock().alloc_pages(pages, align)?;
        Ok(unsafe { NonNull::new_unchecked(addr as *mut u8) })
    }

    unsafe fn large_dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        let pages = align_up(layout.size(), PAGE_SIZE) / PAGE_SIZE;
        self.buddy
            .lock()
            .dealloc_pages(ptr.as_ptr() as usize, pages);
    }
}

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
