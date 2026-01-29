//! Global allocator implementation for Axvisor.
//!
//! This module implements a global allocator that coordinates between
//! buddy page allocator and slab byte allocator for optimal performance.

extern crate alloc;

use crate::{AllocError, AllocResult, BaseAllocator, ByteAllocator, PageAllocator};
use core::alloc::Layout;
use core::ptr::NonNull;
#[cfg(feature = "tracking")]
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::{AtomicBool, Ordering};

#[cfg(feature = "tracking")]
use super::buddy::BuddyStats;
use super::page_allocator::CompositePageAllocator;
use super::slab::{PageAllocatorForSlab, SlabByteAllocator};

#[cfg(feature = "log")]
use log::error;

const MIN_HEAP_SIZE: usize = 0x8000; // 32KB minimum heap

/// Memory usage statistics
#[cfg(feature = "tracking")]
#[derive(Debug, Clone, Copy)]
pub struct UsageStats {
    pub total_pages: usize,
    pub used_pages: usize,
    pub free_pages: usize,
    pub slab_bytes: usize,
    pub heap_bytes: usize,
}

#[cfg(feature = "tracking")]
impl Default for UsageStats {
    fn default() -> Self {
        Self {
            total_pages: 0,
            used_pages: 0,
            free_pages: 0,
            slab_bytes: 0,
            heap_bytes: 0,
        }
    }
}

/// Internal atomic representation of usage statistics
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

/// Global allocator that coordinates composite and slab allocators
pub struct GlobalAllocator<const PAGE_SIZE: usize = { crate::DEFAULT_PAGE_SIZE }> {
    page_allocator: CompositePageAllocator<PAGE_SIZE>,
    slab_allocator: SlabByteAllocator<PAGE_SIZE>,
    #[cfg(feature = "tracking")]
    stats: UsageStatsAtomic,
    initialized: AtomicBool,
}

impl<const PAGE_SIZE: usize> GlobalAllocator<PAGE_SIZE> {
    pub const fn new() -> Self {
        Self {
            page_allocator: CompositePageAllocator::<PAGE_SIZE>::new(),
            slab_allocator: SlabByteAllocator::<PAGE_SIZE>::new(),
            #[cfg(feature = "tracking")]
            stats: UsageStatsAtomic::new(),
            initialized: AtomicBool::new(false),
        }
    }

    /// Set the address translator so that the underlying page allocator can
    /// reason about physical address ranges (e.g. low-memory regions below 4GiB).
    pub fn set_addr_translator(&mut self, translator: &'static dyn crate::AddrTranslator) {
        self.page_allocator.set_addr_translator(translator);
    }

    /// Allocate low-memory pages (physical address < 4GiB).
    /// This is a thin wrapper over the composite allocator's lowmem API.
    pub fn alloc_dma32_pages(&mut self, num_pages: usize, alignment: usize) -> AllocResult<usize> {
        if !self.initialized.load(Ordering::SeqCst) {
            error!("global allocator: Allocator not initialized");
            return Err(AllocError::NoMemory);
        }
        self.page_allocator.alloc_pages_lowmem(num_pages, alignment)
    }

    /// Initialize allocator with given memory region
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use buddy_slab_allocator::GlobalAllocator;
    ///
    /// const PAGE_SIZE: usize = 0x1000;
    /// let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
    /// allocator.init(0x8000_0000, 16 * 1024 * 1024).unwrap();
    /// ```
    pub fn init(&mut self, start_vaddr: usize, size: usize) -> AllocResult<()> {
        if size <= MIN_HEAP_SIZE {
            return Err(AllocError::InvalidParam);
        }

        self.page_allocator.init(start_vaddr, size);

        self.slab_allocator.init();

        {
            let page_alloc_ptr = &mut self.page_allocator as *mut CompositePageAllocator<PAGE_SIZE>;
            self.slab_allocator
                .set_page_allocator(page_alloc_ptr as *mut dyn PageAllocatorForSlab);
        }

        // Update statistics
        #[cfg(feature = "tracking")]
        {
            self.stats
                .total_pages
                .store(self.page_allocator.total_pages(), Ordering::Relaxed);
            self.stats
                .used_pages
                .store(self.page_allocator.used_pages(), Ordering::Relaxed);
            self.stats
                .free_pages
                .store(self.page_allocator.available_pages(), Ordering::Relaxed);
        }

        self.initialized.store(true, Ordering::SeqCst);
        Ok(())
    }

    /// Dynamically add memory region to allocator
    pub fn add_memory(&mut self, start_vaddr: usize, size: usize) -> AllocResult<()> {
        self.page_allocator.add_memory(start_vaddr, size)?;

        // Update statistics
        #[cfg(feature = "tracking")]
        {
            self.stats
                .total_pages
                .store(self.page_allocator.total_pages(), Ordering::Relaxed);
            self.stats
                .free_pages
                .store(self.page_allocator.available_pages(), Ordering::Relaxed);
        }

        Ok(())
    }

    /// Smart allocation based on size
    ///
    /// Small allocations (≤2048 bytes) use slab allocator,
    /// larger allocations use page allocator.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use buddy_slab_allocator::GlobalAllocator;
    /// use core::alloc::Layout;
    ///
    /// const PAGE_SIZE: usize = 0x1000;
    /// let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
    /// allocator.init(0x8000_0000, 16 * 1024 * 1024).unwrap();
    ///
    /// let layout = Layout::from_size_align(64, 8).unwrap();
    /// let ptr = allocator.alloc(layout).unwrap();
    /// allocator.dealloc(ptr, layout);
    /// ```
    pub fn alloc(&mut self, layout: Layout) -> AllocResult<NonNull<u8>> {
        if !self.initialized.load(Ordering::SeqCst) {
            error!("global allocator: Allocator not initialized");
            return Err(AllocError::NoMemory);
        }

        if layout.size() <= 2048 && layout.align() <= 2048 {
            // Try slab allocator first
            match self.slab_allocator.alloc(layout) {
                Ok(ptr) => {
                    #[cfg(feature = "tracking")]
                    {
                        self.stats
                            .slab_bytes
                            .fetch_add(layout.size(), Ordering::Relaxed);
                    }
                    return Ok(ptr);
                }
                Err(e) => {
                    // Slab allocator should handle all requests that satisfy constraints
                    // If it fails, it's a real error (e.g., out of memory)
                    // Log for debugging
                    error!(
                        "global allocator: Slab allocator failed for layout {:?}, error: {:?}, falling back to page allocator",
                        layout, e
                    );
                    return Err(e);
                }
            }
        }

        let pages_needed = (layout.size() + PAGE_SIZE - 1) / PAGE_SIZE;

        let addr =
            PageAllocator::alloc_pages(&mut self.page_allocator, pages_needed, layout.align())?;
        let ptr = unsafe { NonNull::new_unchecked(addr as *mut u8) };

        #[cfg(feature = "tracking")]
        {
            self.stats
                .used_pages
                .fetch_add(pages_needed, Ordering::Relaxed);
            self.stats
                .free_pages
                .fetch_sub(pages_needed, Ordering::Relaxed);
            self.stats
                .heap_bytes
                .fetch_add(layout.size(), Ordering::Relaxed);
        }

        Ok(ptr)
    }

    /// Allocate pages
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use buddy_slab_allocator::{GlobalAllocator, PageAllocator};
    ///
    /// const PAGE_SIZE: usize = 0x1000;
    /// let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
    /// allocator.init(0x8000_0000, 16 * 1024 * 1024).unwrap();
    ///
    /// let addr = allocator.alloc_pages(4, PAGE_SIZE).unwrap();
    /// allocator.dealloc_pages(addr, 4);
    /// ```
    pub fn alloc_pages(&mut self, num_pages: usize, alignment: usize) -> AllocResult<usize> {
        if !self.initialized.load(Ordering::SeqCst) {
            return Err(AllocError::NoMemory);
        }

        let addr = PageAllocator::alloc_pages(&mut self.page_allocator, num_pages, alignment)?;

        // Update statistics
        #[cfg(feature = "tracking")]
        {
            self.stats
                .used_pages
                .fetch_add(num_pages, Ordering::Relaxed);
            self.stats
                .free_pages
                .fetch_sub(num_pages, Ordering::Relaxed);
        }

        Ok(addr)
    }

    /// Deallocate memory
    pub fn dealloc(&mut self, ptr: NonNull<u8>, layout: Layout) {
        if !self.initialized.load(Ordering::SeqCst) {
            error!("global allocator: Deallocating memory before initializing");
            return;
        }

        if layout.size() <= 2048 && layout.align() <= 2048 {
            // This memory must have been allocated by slab allocator
            // If dealloc fails (not found in slab), it's a critical error
            self.slab_allocator.dealloc(ptr, layout);
            #[cfg(feature = "tracking")]
            {
                saturating_sub_atomic(&self.stats.slab_bytes, layout.size());
            }
            return;
        }

        // This memory was allocated by page allocator
        let pages_needed = (layout.size() + PAGE_SIZE - 1) / PAGE_SIZE;
        PageAllocator::dealloc_pages(
            &mut self.page_allocator,
            ptr.as_ptr() as usize,
            pages_needed,
        );
        #[cfg(feature = "tracking")]
        {
            saturating_sub_atomic(&self.stats.used_pages, pages_needed);
            self.stats
                .free_pages
                .fetch_add(pages_needed, Ordering::Relaxed);
            saturating_sub_atomic(&self.stats.heap_bytes, layout.size());
        }
    }

    /// Deallocate pages
    pub fn dealloc_pages(&mut self, pos: usize, num_pages: usize) {
        if !self.initialized.load(Ordering::SeqCst) {
            return;
        }

        PageAllocator::dealloc_pages(&mut self.page_allocator, pos, num_pages);

        // Update statistics
        #[cfg(feature = "tracking")]
        {
            saturating_sub_atomic(&self.stats.used_pages, num_pages);
            self.stats
                .free_pages
                .fetch_add(num_pages, Ordering::Relaxed);
        }
    }

    /// Reallocate memory
    pub fn realloc(&mut self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
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

        let new_layout = Layout::from_size_align(new_size, layout.align())
            .unwrap_or_else(|_| Layout::new::<u8>());

        // If new size fits in old allocation, return old pointer
        if new_size <= layout.size() {
            return ptr;
        }

        // Allocate new memory and copy
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
}

impl<const PAGE_SIZE: usize> GlobalAllocator<PAGE_SIZE> {
    /// Get memory statistics
    #[cfg(feature = "tracking")]
    pub fn get_stats(&self) -> UsageStats {
        self.stats.snapshot()
    }

    /// Get buddy allocator statistics
    #[cfg(feature = "tracking")]
    pub fn get_buddy_stats(&self) -> BuddyStats {
        self.page_allocator.get_buddy_stats()
    }
}

impl<const PAGE_SIZE: usize> Default for GlobalAllocator<PAGE_SIZE> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const PAGE_SIZE: usize> BaseAllocator for GlobalAllocator<PAGE_SIZE> {
    fn init(&mut self, start: usize, size: usize) {
        self.page_allocator.init(start, size);
    }

    fn add_memory(&mut self, start: usize, size: usize) -> AllocResult {
        self.page_allocator.add_memory(start, size)
    }
}

impl<const PAGE_SIZE: usize> PageAllocator for GlobalAllocator<PAGE_SIZE> {
    const PAGE_SIZE: usize = PAGE_SIZE;

    fn alloc_pages(&mut self, num_pages: usize, alignment: usize) -> AllocResult<usize> {
        if !self.initialized.load(Ordering::SeqCst) {
            return Err(AllocError::NoMemory);
        }

        let addr = <CompositePageAllocator<PAGE_SIZE> as PageAllocator>::alloc_pages(
            &mut self.page_allocator,
            num_pages,
            alignment,
        )?;

        // Update statistics
        #[cfg(feature = "tracking")]
        {
            self.stats
                .used_pages
                .fetch_add(num_pages, Ordering::Relaxed);
            self.stats
                .free_pages
                .fetch_sub(num_pages, Ordering::Relaxed);
        }

        Ok(addr)
    }

    fn dealloc_pages(&mut self, pos: usize, num_pages: usize) {
        if !self.initialized.load(Ordering::SeqCst) {
            return;
        }

        <CompositePageAllocator<PAGE_SIZE> as PageAllocator>::dealloc_pages(
            &mut self.page_allocator,
            pos,
            num_pages,
        );

        // Update statistics
        #[cfg(feature = "tracking")]
        {
            saturating_sub_atomic(&self.stats.used_pages, num_pages);
            self.stats
                .free_pages
                .fetch_add(num_pages, Ordering::Relaxed);
        }
    }

    fn alloc_pages_at(
        &mut self,
        base: usize,
        num_pages: usize,
        alignment: usize,
    ) -> AllocResult<usize> {
        if !self.initialized.load(Ordering::SeqCst) {
            return Err(AllocError::NoMemory);
        }

        let addr = <CompositePageAllocator<PAGE_SIZE> as PageAllocator>::alloc_pages_at(
            &mut self.page_allocator,
            base,
            num_pages,
            alignment,
        )?;

        // Update statistics
        #[cfg(feature = "tracking")]
        {
            self.stats
                .used_pages
                .fetch_add(num_pages, Ordering::Relaxed);
            self.stats
                .free_pages
                .fetch_sub(num_pages, Ordering::Relaxed);
        }

        Ok(addr)
    }

    fn total_pages(&self) -> usize {
        self.page_allocator.total_pages()
    }

    fn used_pages(&self) -> usize {
        self.page_allocator.used_pages()
    }

    fn available_pages(&self) -> usize {
        self.page_allocator.available_pages()
    }
}
