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

/// Unified allocator: buddy page allocator + per-CPU slab caches.
pub struct GlobalAllocator<const PAGE_SIZE: usize = 0x1000> {
    buddy: SpinMutex<BuddyAllocator<PAGE_SIZE>>,
    per_cpu_slabs: *mut SpinMutex<SlabAllocator<PAGE_SIZE>>,
    cpu_count: usize,
    os: Option<&'static dyn OsImpl>,
    initialized: AtomicBool,
}

// SAFETY: All mutable state is behind SpinMutex or AtomicBool.
// `per_cpu_slabs` is a raw pointer into the metadata region whose lifetime
// is managed by the caller (same as BuddyAllocator::meta).
unsafe impl<const PAGE_SIZE: usize> Sync for GlobalAllocator<PAGE_SIZE> {}
unsafe impl<const PAGE_SIZE: usize> Send for GlobalAllocator<PAGE_SIZE> {}

impl<const PAGE_SIZE: usize> GlobalAllocator<PAGE_SIZE> {
    // ------------------------------------------------------------------
    // Metadata sizing
    // ------------------------------------------------------------------

    /// Calculate the total metadata region size needed.
    ///
    /// The metadata region is laid out as:
    /// ```text
    /// [ PageMeta[max_pages] | padding | SpinMutex<SlabAllocator>[cpu_count] ]
    /// ```
    pub const fn required_metadata_size(heap_size: usize, cpu_count: usize) -> usize {
        let buddy_meta = BuddyAllocator::<PAGE_SIZE>::required_meta_size(heap_size);
        // Align slab array to its natural alignment.
        let slab_align = core::mem::align_of::<SpinMutex<SlabAllocator<PAGE_SIZE>>>();
        let slab_offset = (buddy_meta + slab_align - 1) & !(slab_align - 1);
        let slab_size = core::mem::size_of::<SpinMutex<SlabAllocator<PAGE_SIZE>>>() * cpu_count;
        slab_offset + slab_size
    }

    /// Required alignment for the metadata region.
    pub const fn required_metadata_align() -> usize {
        let a1 = core::mem::align_of::<crate::buddy::PageMeta>();
        let a2 = core::mem::align_of::<SpinMutex<SlabAllocator<PAGE_SIZE>>>();
        if a1 > a2 {
            a1
        } else {
            a2
        }
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

    /// Initialise the allocator.
    ///
    /// # Arguments
    /// - `meta` / `meta_size` — writable metadata region (see [`required_metadata_size`]).
    /// - `heap_start` / `heap_size` — the heap virtual address range to manage.
    /// - `cpu_count` — number of CPUs (≥ 1).
    /// - `os` — platform abstraction.
    ///
    /// # Safety
    /// - The metadata and heap regions must not overlap.
    /// - `meta` must be aligned to [`required_metadata_align`].
    /// - Both regions must remain valid for the lifetime of this allocator.
    pub unsafe fn init(
        &self,
        meta: *mut u8,
        meta_size: usize,
        heap_start: usize,
        heap_size: usize,
        cpu_count: usize,
        os: &'static dyn OsImpl,
    ) -> AllocResult {
        if cpu_count == 0 || meta.is_null() {
            return Err(AllocError::InvalidParam);
        }
        let required = Self::required_metadata_size(heap_size, cpu_count);
        if meta_size < required {
            return Err(AllocError::InvalidParam);
        }

        // --- Partition metadata region ---
        let buddy_meta_size = BuddyAllocator::<PAGE_SIZE>::required_meta_size(heap_size);
        let buddy_meta_ptr = meta;

        let slab_align = core::mem::align_of::<SpinMutex<SlabAllocator<PAGE_SIZE>>>();
        let slab_offset = align_up(buddy_meta_size, slab_align);
        let slab_ptr = meta.add(slab_offset) as *mut SpinMutex<SlabAllocator<PAGE_SIZE>>;

        // --- Init buddy ---
        let mut buddy = self.buddy.lock();
        buddy.init(
            buddy_meta_ptr,
            buddy_meta_size,
            heap_start,
            heap_size,
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
            "GlobalAllocator: {} CPUs, heap {:#x}+{:#x}, meta {:#x}+{:#x}",
            cpu_count,
            heap_start,
            heap_size,
            meta as usize,
            meta_size,
        );

        Ok(())
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
                // Align to slab_bytes so base_from_obj_addr works via address masking.
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
        let base = SlabPageHeader::base_from_obj_addr(ptr.as_ptr() as usize, slab_bytes);
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
