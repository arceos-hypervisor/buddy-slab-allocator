//! Global allocator implementation.
//!
//! This module implements a multi-core global allocator that coordinates
//! between a shared page allocator backend and per-CPU slab frontends.

extern crate alloc;

use crate::os::set_os_provider;
use crate::slab::slab_node::SlabNode;
use crate::slab::{SizeClass, SlabAllocDecision, SlabByteAllocator, SlabDeallocDecision};
use crate::{AllocError, AllocResult};
use core::alloc::Layout;
use core::mem::{align_of, size_of};
use core::ptr::NonNull;
use core::slice;
#[cfg(feature = "tracking")]
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::{AtomicBool, Ordering};
use log::error;
use spin::Mutex;

#[cfg(feature = "tracking")]
use super::buddy::BuddyStats;
use super::page_allocator::CompositePageAllocator;

const MIN_HEAP_SIZE: usize = 0x8000;

/// Memory usage statistics.
#[cfg(feature = "tracking")]
#[derive(Debug, Clone, Copy, Default)]
pub struct UsageStats {
    pub total_pages: usize,
    pub used_pages: usize,
    pub free_pages: usize,
    pub slab_bytes: usize,
    pub heap_bytes: usize,
}

#[cfg(feature = "tracking")]
struct UsageStatsAtomic {
    total_pages: AtomicUsize,
    used_pages: AtomicUsize,
    free_pages: AtomicUsize,
    slab_bytes: AtomicUsize,
    heap_bytes: AtomicUsize,
}

#[cfg(feature = "tracking")]
impl UsageStatsAtomic {
    const fn new() -> Self {
        Self {
            total_pages: AtomicUsize::new(0),
            used_pages: AtomicUsize::new(0),
            free_pages: AtomicUsize::new(0),
            slab_bytes: AtomicUsize::new(0),
            heap_bytes: AtomicUsize::new(0),
        }
    }

    fn snapshot(&self) -> UsageStats {
        UsageStats {
            total_pages: self.total_pages.load(Ordering::Relaxed),
            used_pages: self.used_pages.load(Ordering::Relaxed),
            free_pages: self.free_pages.load(Ordering::Relaxed),
            slab_bytes: self.slab_bytes.load(Ordering::Relaxed),
            heap_bytes: self.heap_bytes.load(Ordering::Relaxed),
        }
    }
}

#[cfg(feature = "tracking")]
#[inline]
fn saturating_sub_atomic(counter: &AtomicUsize, value: usize) {
    let mut prev = counter.load(Ordering::Relaxed);
    loop {
        let new = prev.saturating_sub(value);
        match counter.compare_exchange(prev, new, Ordering::AcqRel, Ordering::Relaxed) {
            Ok(_) => break,
            Err(actual) => prev = actual,
        }
    }
}

#[derive(Clone, Copy, Default)]
struct MetadataRegionInfo {
    start: usize,
    size: usize,
}

struct PerCpuSlabSlot<const PAGE_SIZE: usize> {
    slab: Mutex<SlabByteAllocator<PAGE_SIZE>>,
}

impl<const PAGE_SIZE: usize> PerCpuSlabSlot<PAGE_SIZE> {
    const fn new() -> Self {
        Self {
            slab: Mutex::new(SlabByteAllocator::new()),
        }
    }
}

/// Multi-core global allocator facade.
pub struct GlobalAllocator<const PAGE_SIZE: usize = { crate::DEFAULT_PAGE_SIZE }> {
    buddy: Mutex<CompositePageAllocator<PAGE_SIZE>>,
    slab_slots_ptr: Option<NonNull<PerCpuSlabSlot<PAGE_SIZE>>>,
    cpu_count: usize,
    metadata_region: MetadataRegionInfo,
    os: &'static dyn crate::Os,
    #[cfg(feature = "tracking")]
    stats: UsageStatsAtomic,
    initialized: AtomicBool,
}

impl<const PAGE_SIZE: usize> GlobalAllocator<PAGE_SIZE> {
    pub const fn new() -> Self {
        Self {
            buddy: Mutex::new(CompositePageAllocator::<PAGE_SIZE>::new()),
            slab_slots_ptr: None,
            cpu_count: 0,
            metadata_region: MetadataRegionInfo { start: 0, size: 0 },
            os: &crate::NoImplOs,
            #[cfg(feature = "tracking")]
            stats: UsageStatsAtomic::new(),
            initialized: AtomicBool::new(false),
        }
    }

    pub fn required_metadata_size(cpu_count: usize) -> usize {
        if cpu_count == 0 {
            return 0;
        }
        let slot_size = size_of::<PerCpuSlabSlot<PAGE_SIZE>>();
        let slot_align = align_of::<PerCpuSlabSlot<PAGE_SIZE>>();
        let size = slot_size.saturating_mul(cpu_count);
        crate::align_up(size, slot_align)
    }

    pub fn required_metadata_align() -> usize {
        align_of::<PerCpuSlabSlot<PAGE_SIZE>>()
    }

    /// Set the address translator so that the underlying page allocator can
    /// reason about physical address ranges (e.g. low-memory regions below 4GiB).
    pub fn set_addr_translator(&self, translator: &'static dyn crate::AddrTranslator) {
        self.buddy.lock().set_addr_translator(translator);
    }

    fn slab_slots(&self) -> &[PerCpuSlabSlot<PAGE_SIZE>] {
        let ptr = self
            .slab_slots_ptr
            .expect("global allocator slab slots accessed before init");
        unsafe { slice::from_raw_parts(ptr.as_ptr(), self.cpu_count) }
    }

    fn slab_slot(&self, cpu_id: usize) -> AllocResult<&PerCpuSlabSlot<PAGE_SIZE>> {
        if !self.initialized.load(Ordering::SeqCst) {
            return Err(AllocError::NoMemory);
        }
        if cpu_id >= self.cpu_count {
            return Err(AllocError::InvalidParam);
        }
        Ok(&self.slab_slots()[cpu_id])
    }

    fn current_cpu_idx_checked(&self) -> AllocResult<usize> {
        let cpu_id = self.os.current_cpu_idx();
        if cpu_id >= self.cpu_count {
            error!(
                "global allocator: OS reported cpu_id {} >= cpu_count {}",
                cpu_id, self.cpu_count
            );
            return Err(AllocError::InvalidParam);
        }
        Ok(cpu_id)
    }

    fn owner_cpu_from_ptr(&self, ptr: NonNull<u8>, layout: Layout) -> Option<usize> {
        let size_class = SizeClass::from_layout(layout)?;
        let slab_bytes = size_class.slab_bytes(PAGE_SIZE);
        let slab_base = (ptr.as_ptr() as usize / slab_bytes) * slab_bytes;
        let node = SlabNode::new(slab_base, size_class);
        if node.is_valid_for_size_class() {
            Some(node.owner_cpu())
        } else {
            None
        }
    }

    fn update_page_stats_after_alloc(&self, num_pages: usize) {
        #[cfg(feature = "tracking")]
        {
            self.stats
                .used_pages
                .fetch_add(num_pages, Ordering::Relaxed);
            self.stats
                .free_pages
                .fetch_sub(num_pages, Ordering::Relaxed);
        }
        #[cfg(not(feature = "tracking"))]
        let _ = num_pages;
    }

    fn update_page_stats_after_free(&self, num_pages: usize) {
        #[cfg(feature = "tracking")]
        {
            saturating_sub_atomic(&self.stats.used_pages, num_pages);
            self.stats
                .free_pages
                .fetch_add(num_pages, Ordering::Relaxed);
        }
        #[cfg(not(feature = "tracking"))]
        let _ = num_pages;
    }

    /// Initialize the allocator with metadata storage, memory region, CPU topology and OS hooks.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `[meta_start, meta_start + meta_size)` is valid writable memory
    /// for the lifetime of the allocator and is not used for any other purpose.
    pub unsafe fn init(
        &mut self,
        meta_start: usize,
        meta_size: usize,
        heap_start: usize,
        heap_size: usize,
        cpu_count: usize,
        os: &'static dyn crate::Os,
    ) -> AllocResult<()> {
        if self.initialized.load(Ordering::SeqCst) {
            return Err(AllocError::InvalidParam);
        }
        if cpu_count == 0 || heap_size <= MIN_HEAP_SIZE {
            return Err(AllocError::InvalidParam);
        }
        if !meta_start.is_multiple_of(Self::required_metadata_align()) {
            return Err(AllocError::InvalidParam);
        }
        if meta_size < Self::required_metadata_size(cpu_count) {
            return Err(AllocError::NoMemory);
        }

        let slots_ptr = meta_start as *mut PerCpuSlabSlot<PAGE_SIZE>;
        for idx in 0..cpu_count {
            slots_ptr.add(idx).write(PerCpuSlabSlot::new());
        }

        self.slab_slots_ptr = Some(NonNull::new(slots_ptr).ok_or(AllocError::InvalidParam)?);
        self.cpu_count = cpu_count;
        self.metadata_region = MetadataRegionInfo {
            start: meta_start,
            size: meta_size,
        };
        self.os = os;

        self.buddy.get_mut().init(heap_start, heap_size);

        #[cfg(feature = "tracking")]
        {
            let buddy = self.buddy.get_mut();
            self.stats
                .total_pages
                .store(buddy.total_pages(), Ordering::Relaxed);
            self.stats
                .used_pages
                .store(buddy.used_pages(), Ordering::Relaxed);
            self.stats
                .free_pages
                .store(buddy.available_pages(), Ordering::Relaxed);
        }

        set_os_provider(os);
        self.initialized.store(true, Ordering::SeqCst);
        Ok(())
    }

    pub fn add_memory(&self, start_vaddr: usize, size: usize) -> AllocResult<()> {
        if !self.initialized.load(Ordering::SeqCst) {
            return Err(AllocError::NoMemory);
        }

        let mut buddy = self.buddy.lock();
        buddy.add_memory(start_vaddr, size)?;

        #[cfg(feature = "tracking")]
        {
            self.stats
                .total_pages
                .store(buddy.total_pages(), Ordering::Relaxed);
            self.stats
                .free_pages
                .store(buddy.available_pages(), Ordering::Relaxed);
        }

        Ok(())
    }

    pub fn alloc_dma32_pages(&self, num_pages: usize, alignment: usize) -> AllocResult<usize> {
        if !self.initialized.load(Ordering::SeqCst) {
            error!("global allocator: Allocator not initialized");
            return Err(AllocError::NoMemory);
        }

        let mut buddy = self.buddy.lock();
        let addr = buddy.alloc_pages_lowmem(num_pages, alignment)?;
        self.update_page_stats_after_alloc(num_pages);
        Ok(addr)
    }

    pub fn alloc(&self, layout: Layout) -> AllocResult<NonNull<u8>> {
        if !self.initialized.load(Ordering::SeqCst) {
            error!("global allocator: Allocator not initialized");
            return Err(AllocError::NoMemory);
        }

        if layout.size() <= 2048 && layout.align() <= 2048 {
            let cpu_id = self.current_cpu_idx_checked()?;

            loop {
                let decision = {
                    let slot = self.slab_slot(cpu_id)?;
                    let mut slab = slot.slab.lock();
                    slab.alloc(layout)?
                };

                match decision {
                    SlabAllocDecision::Allocated(ptr, _) => {
                        #[cfg(feature = "tracking")]
                        {
                            self.stats
                                .slab_bytes
                                .fetch_add(layout.size(), Ordering::Relaxed);
                        }
                        return Ok(ptr);
                    }
                    SlabAllocDecision::NeedsRefill {
                        size_class,
                        page_count,
                        slab_bytes,
                    } => {
                        let slab_base = {
                            let mut buddy = self.buddy.lock();
                            let addr = buddy.alloc_pages(page_count, slab_bytes)?;
                            self.update_page_stats_after_alloc(page_count);
                            addr
                        };

                        let slot = self.slab_slot(cpu_id)?;
                        let mut slab = slot.slab.lock();
                        slab.provide_slab(size_class, cpu_id, slab_base, slab_bytes)?;
                    }
                }
            }
        }

        let pages_needed = layout.size().div_ceil(PAGE_SIZE);
        let addr = {
            let mut buddy = self.buddy.lock();
            buddy.alloc_pages(pages_needed, layout.align())?
        };
        self.update_page_stats_after_alloc(pages_needed);
        #[cfg(feature = "tracking")]
        {
            self.stats
                .heap_bytes
                .fetch_add(layout.size(), Ordering::Relaxed);
        }
        Ok(unsafe { NonNull::new_unchecked(addr as *mut u8) })
    }

    pub fn alloc_pages(&self, num_pages: usize, alignment: usize) -> AllocResult<usize> {
        if !self.initialized.load(Ordering::SeqCst) {
            return Err(AllocError::NoMemory);
        }

        let addr = {
            let mut buddy = self.buddy.lock();
            buddy.alloc_pages(num_pages, alignment)?
        };
        self.update_page_stats_after_alloc(num_pages);
        Ok(addr)
    }

    pub fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        if !self.initialized.load(Ordering::SeqCst) {
            error!("global allocator: Deallocating memory before initializing");
            return;
        }

        if layout.size() <= 2048 && layout.align() <= 2048 {
            let owner_cpu = self
                .owner_cpu_from_ptr(ptr, layout)
                .unwrap_or_else(|| self.os.current_cpu_idx());
            if let Ok(slot) = self.slab_slot(owner_cpu) {
                let decision = {
                    let mut slab = slot.slab.lock();
                    let decision = slab.dealloc(ptr, layout);
                    #[cfg(feature = "tracking")]
                    {
                        let actually_deallocated = match &decision {
                            SlabDeallocDecision::Done {
                                actually_deallocated,
                                ..
                            }
                            | SlabDeallocDecision::ReleaseSlab {
                                actually_deallocated,
                                ..
                            } => *actually_deallocated,
                        };
                        if actually_deallocated {
                            saturating_sub_atomic(&self.stats.slab_bytes, layout.size());
                        }
                    }
                    decision
                };

                if let SlabDeallocDecision::ReleaseSlab {
                    slab_base,
                    page_count,
                    ..
                } = decision
                {
                    let mut buddy = self.buddy.lock();
                    buddy.dealloc_pages(slab_base, page_count);
                    self.update_page_stats_after_free(page_count);
                }
            }
            return;
        }

        let pages_needed = layout.size().div_ceil(PAGE_SIZE);
        {
            let mut buddy = self.buddy.lock();
            buddy.dealloc_pages(ptr.as_ptr() as usize, pages_needed);
        }
        self.update_page_stats_after_free(pages_needed);
        #[cfg(feature = "tracking")]
        {
            saturating_sub_atomic(&self.stats.heap_bytes, layout.size());
        }
    }

    pub fn dealloc_pages(&self, pos: usize, num_pages: usize) {
        if !self.initialized.load(Ordering::SeqCst) {
            return;
        }

        {
            let mut buddy = self.buddy.lock();
            buddy.dealloc_pages(pos, num_pages);
        }
        self.update_page_stats_after_free(num_pages);
    }

    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    pub fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        if new_size == 0 {
            if let Some(ptr) = NonNull::new(ptr) {
                self.dealloc(ptr, layout);
            }
            return core::ptr::null_mut();
        }

        if ptr.is_null() {
            let new_layout = Layout::from_size_align(new_size, layout.align())
                .unwrap_or_else(|_| Layout::new::<u8>());
            return match self.alloc(new_layout) {
                Ok(ptr) => ptr.as_ptr(),
                Err(_) => core::ptr::null_mut(),
            };
        }

        if new_size <= layout.size() {
            return ptr;
        }

        let new_layout = Layout::from_size_align(new_size, layout.align())
            .unwrap_or_else(|_| Layout::new::<u8>());
        match self.alloc(new_layout) {
            Ok(new_ptr) => {
                let new_ptr = new_ptr.as_ptr();
                unsafe {
                    core::ptr::copy_nonoverlapping(
                        ptr,
                        new_ptr,
                        core::cmp::min(layout.size(), new_size),
                    );
                }
                if let Some(ptr) = NonNull::new(ptr) {
                    self.dealloc(ptr, layout);
                }
                new_ptr
            }
            Err(_) => core::ptr::null_mut(),
        }
    }

    pub fn total_pages(&self) -> usize {
        #[cfg(feature = "tracking")]
        {
            return self.stats.total_pages.load(Ordering::Relaxed);
        }
        #[cfg(not(feature = "tracking"))]
        {
            self.buddy.lock().total_pages()
        }
    }

    pub fn used_pages(&self) -> usize {
        #[cfg(feature = "tracking")]
        {
            return self.stats.used_pages.load(Ordering::Relaxed);
        }
        #[cfg(not(feature = "tracking"))]
        {
            self.buddy.lock().used_pages()
        }
    }

    pub fn available_pages(&self) -> usize {
        #[cfg(feature = "tracking")]
        {
            return self.stats.free_pages.load(Ordering::Relaxed);
        }
        #[cfg(not(feature = "tracking"))]
        {
            self.buddy.lock().available_pages()
        }
    }

    pub fn cpu_count(&self) -> usize {
        self.cpu_count
    }

    pub fn metadata_region(&self) -> (usize, usize) {
        (self.metadata_region.start, self.metadata_region.size)
    }

    #[cfg(feature = "tracking")]
    pub fn get_stats(&self) -> UsageStats {
        self.stats.snapshot()
    }

    #[cfg(feature = "tracking")]
    pub fn get_buddy_stats(&self) -> BuddyStats {
        self.buddy.lock().get_buddy_stats()
    }
}

impl<const PAGE_SIZE: usize> Default for GlobalAllocator<PAGE_SIZE> {
    fn default() -> Self {
        Self::new()
    }
}
