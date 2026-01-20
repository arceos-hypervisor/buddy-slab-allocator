//! Global allocator implementation for Axvisor.
//!
//! This module implements a global allocator that coordinates between
//! buddy page allocator and slab byte allocator for optimal performance.

extern crate alloc;

use crate::{AllocError, AllocResult, BaseAllocator, ByteAllocator, PageAllocator};
use core::alloc::Layout;
use core::ptr::NonNull;
use core::sync::atomic::{AtomicBool, Ordering};

#[cfg(feature = "tracking")]
use super::buddy::BuddyStats;
use super::page_allocator::CompositePageAllocator;
use super::slab::{PageAllocatorForSlab, SlabByteAllocator};
use kspin::SpinNoIrq;

#[cfg(feature = "log")]
use log::{error, warn};

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

/// Global allocator that coordinates composite and slab allocators
pub struct GlobalAllocator<const PAGE_SIZE: usize = { crate::DEFAULT_PAGE_SIZE }> {
    page_allocator: SpinNoIrq<CompositePageAllocator<PAGE_SIZE>>,
    slab_allocator: SpinNoIrq<SlabByteAllocator<PAGE_SIZE>>,
    #[cfg(feature = "tracking")]
    stats: SpinNoIrq<UsageStats>,
    initialized: AtomicBool,
}

impl<const PAGE_SIZE: usize> GlobalAllocator<PAGE_SIZE> {
    pub const fn new() -> Self {
        Self {
            page_allocator: SpinNoIrq::new(CompositePageAllocator::<PAGE_SIZE>::new()),
            slab_allocator: SpinNoIrq::new(SlabByteAllocator::<PAGE_SIZE>::new()),
            #[cfg(feature = "tracking")]
            stats: SpinNoIrq::new(UsageStats {
                total_pages: 0,
                used_pages: 0,
                free_pages: 0,
                heap_bytes: 0,
                slab_bytes: 0,
            }),
            initialized: AtomicBool::new(false),
        }
    }

    /// Initialize allocator with given memory region
    pub fn init(&self, start_vaddr: usize, size: usize) -> AllocResult<()> {
        if size <= MIN_HEAP_SIZE {
            return Err(AllocError::InvalidParam);
        }

        self.page_allocator.lock().init(start_vaddr, size);

        self.slab_allocator.lock().init();

        {
            let page_alloc_ptr =
                &mut *self.page_allocator.lock() as *mut CompositePageAllocator<PAGE_SIZE>;
            self.slab_allocator
                .lock()
                .set_page_allocator(page_alloc_ptr as *mut dyn PageAllocatorForSlab);
        }

        // Update statistics
        #[cfg(feature = "tracking")]
        {
            let page_alloc = self.page_allocator.lock();
            let mut stats = self.stats.lock();
            stats.total_pages = page_alloc.total_pages();
            stats.used_pages = page_alloc.used_pages();
            stats.free_pages = page_alloc.available_pages();
        }

        self.initialized.store(true, Ordering::SeqCst);
        Ok(())
    }

    /// Dynamically add memory region to allocator
    pub fn add_memory(&self, start_vaddr: usize, size: usize) -> AllocResult<()> {
        self.page_allocator.lock().add_memory(start_vaddr, size)?;

        // Update statistics
        #[cfg(feature = "tracking")]
        {
            let page_alloc = self.page_allocator.lock();
            let mut stats = self.stats.lock();
            stats.total_pages = page_alloc.total_pages();
            stats.free_pages = page_alloc.available_pages();
        }

        Ok(())
    }

    /// Smart allocation based on size
    pub fn alloc(&self, layout: Layout) -> AllocResult<NonNull<u8>> {
        if !self.initialized.load(Ordering::SeqCst) {
            error!("global allocator: Allocator not initialized");
            return Err(AllocError::NoMemory);
        }

        if layout.size() <= 2048 && layout.align() <= 2048 {
            // Try slab allocator first
            match self.slab_allocator.lock().alloc(layout) {
                Ok(ptr) => {
                    #[cfg(feature = "tracking")]
                    {
                        self.stats.lock().slab_bytes += layout.size();
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

        let addr = PageAllocator::alloc_pages(
            &mut *self.page_allocator.lock(),
            pages_needed,
            layout.align(),
        )?;
        let ptr = unsafe { NonNull::new_unchecked(addr as *mut u8) };

        #[cfg(feature = "tracking")]
        {
            let mut stats = self.stats.lock();
            stats.used_pages += pages_needed;
            stats.free_pages -= pages_needed;
            stats.heap_bytes += layout.size();
        }

        Ok(ptr)
    }

    /// Allocate pages
    pub fn alloc_pages(&self, num_pages: usize, alignment: usize) -> AllocResult<usize> {
        if !self.initialized.load(Ordering::SeqCst) {
            return Err(AllocError::NoMemory);
        }

        let addr =
            PageAllocator::alloc_pages(&mut *self.page_allocator.lock(), num_pages, alignment)?;

        // Update statistics
        #[cfg(feature = "tracking")]
        {
            let mut stats = self.stats.lock();
            stats.used_pages += num_pages;
            stats.free_pages -= num_pages;
        }

        Ok(addr)
    }

    /// Deallocate memory
    pub fn dealloc(&self, ptr: NonNull<u8>, layout: Layout) {
        if !self.initialized.load(Ordering::SeqCst) {
            error!("global allocator: Deallocating memory before initializing");
            return;
        }

        if layout.size() <= 2048 && layout.align() <= 2048 {
            // This memory must have been allocated by slab allocator
            // If dealloc fails (not found in slab), it's a critical error
            self.slab_allocator.lock().dealloc(ptr, layout);
            #[cfg(feature = "tracking")]
            {
                let mut stats = self.stats.lock();
                stats.slab_bytes = stats.slab_bytes.saturating_sub(layout.size());
            }
            return;
        }

        // This memory was allocated by page allocator
        let pages_needed = (layout.size() + PAGE_SIZE - 1) / PAGE_SIZE;
        PageAllocator::dealloc_pages(
            &mut *self.page_allocator.lock(),
            ptr.as_ptr() as usize,
            pages_needed,
        );
        #[cfg(feature = "tracking")]
        {
            let mut stats = self.stats.lock();
            stats.used_pages = stats.used_pages.saturating_sub(pages_needed);
            stats.free_pages += pages_needed;
            stats.heap_bytes = stats.heap_bytes.saturating_sub(layout.size());
        }
    }

    /// Deallocate pages
    pub fn dealloc_pages(&self, pos: usize, num_pages: usize) {
        if !self.initialized.load(Ordering::SeqCst) {
            return;
        }

        PageAllocator::dealloc_pages(&mut *self.page_allocator.lock(), pos, num_pages);

        // Update statistics
        #[cfg(feature = "tracking")]
        {
            let mut stats = self.stats.lock();
            stats.used_pages = stats.used_pages.saturating_sub(num_pages);
            stats.free_pages += num_pages;
        }
    }
}

impl<const PAGE_SIZE: usize> GlobalAllocator<PAGE_SIZE> {
    /// Get memory statistics
    #[cfg(feature = "tracking")]
    pub fn get_stats(&self) -> UsageStats {
        *self.stats.lock()
    }

    /// Get buddy allocator statistics
    #[cfg(feature = "tracking")]
    pub fn get_buddy_stats(&self) -> BuddyStats {
        self.page_allocator.lock().get_buddy_stats()
    }
}

impl<const PAGE_SIZE: usize> Default for GlobalAllocator<PAGE_SIZE> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const PAGE_SIZE: usize> BaseAllocator for GlobalAllocator<PAGE_SIZE> {
    fn init(&mut self, start: usize, size: usize) {
        self.page_allocator.lock().init(start, size);
    }

    fn add_memory(&mut self, start: usize, size: usize) -> AllocResult {
        self.page_allocator.lock().add_memory(start, size)
    }
}

impl<const PAGE_SIZE: usize> PageAllocator for GlobalAllocator<PAGE_SIZE> {
    const PAGE_SIZE: usize = PAGE_SIZE;

    fn alloc_pages(&mut self, num_pages: usize, alignment: usize) -> AllocResult<usize> {
        if !self.initialized.load(Ordering::SeqCst) {
            return Err(AllocError::NoMemory);
        }

        let addr = <CompositePageAllocator<PAGE_SIZE> as PageAllocator>::alloc_pages(
            &mut *self.page_allocator.lock(),
            num_pages,
            alignment,
        )?;

        // Update statistics
        #[cfg(feature = "tracking")]
        {
            let mut stats = self.stats.lock();
            stats.used_pages += num_pages;
            stats.free_pages -= num_pages;
        }

        Ok(addr)
    }

    fn dealloc_pages(&mut self, pos: usize, num_pages: usize) {
        if !self.initialized.load(Ordering::SeqCst) {
            return;
        }

        <CompositePageAllocator<PAGE_SIZE> as PageAllocator>::dealloc_pages(
            &mut *self.page_allocator.lock(),
            pos,
            num_pages,
        );

        // Update statistics
        #[cfg(feature = "tracking")]
        {
            let mut stats = self.stats.lock();
            stats.used_pages = stats.used_pages.saturating_sub(num_pages);
            stats.free_pages += num_pages;
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
            &mut *self.page_allocator.lock(),
            base,
            num_pages,
            alignment,
        )?;

        // Update statistics
        #[cfg(feature = "tracking")]
        {
            let mut stats = self.stats.lock();
            stats.used_pages += num_pages;
            stats.free_pages -= num_pages;
        }

        Ok(addr)
    }

    fn total_pages(&self) -> usize {
        self.page_allocator.lock().total_pages()
    }

    fn used_pages(&self) -> usize {
        self.page_allocator.lock().used_pages()
    }

    fn available_pages(&self) -> usize {
        self.page_allocator.lock().available_pages()
    }
}

unsafe impl<const PAGE_SIZE: usize> core::alloc::GlobalAlloc for GlobalAllocator<PAGE_SIZE> {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if !self.initialized.load(Ordering::SeqCst) {
            warn!("global allocator: Allocator not initialized");
            return core::ptr::null_mut();
        }

        if layout.size() <= 2048 && layout.align() <= 2048 {
            match self.slab_allocator.lock().alloc(layout) {
                Ok(ptr) => {
                    #[cfg(feature = "tracking")]
                    {
                        let mut stats = self.stats.lock();
                        stats.slab_bytes += layout.size();
                    }
                    return ptr.as_ptr();
                }
                Err(_e) => {
                    warn!(
                        "global allocator: Slab allocator failed for layout {:?}, error: {:?}, falling back to page allocator",
                        layout, _e
                    );
                    return core::ptr::null_mut();
                }
            }
        }

        // Use page allocator for large objects or high alignment requirements
        let pages_needed = (layout.size() + Self::PAGE_SIZE - 1) / Self::PAGE_SIZE;
        match PageAllocator::alloc_pages(
            &mut *self.page_allocator.lock(),
            pages_needed,
            layout.align(),
        ) {
            Ok(addr) => {
                #[cfg(feature = "tracking")]
                {
                    let mut stats = self.stats.lock();
                    stats.used_pages += pages_needed;
                    stats.free_pages -= pages_needed;
                    stats.heap_bytes += layout.size();
                }
                addr as *mut u8
            }
            Err(_) => core::ptr::null_mut(),
        }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if let Some(ptr) = NonNull::new(ptr) {
            self.dealloc(ptr, layout);
        }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        if new_size == 0 {
            if let Some(ptr) = NonNull::new(ptr) {
                self.dealloc(ptr, layout);
            }
            return core::ptr::null_mut();
        }

        if ptr.is_null() {
            let new_layout = Layout::from_size_align(new_size, layout.align())
                .unwrap_or_else(|_| Layout::new::<u8>());
            return unsafe { core::alloc::GlobalAlloc::alloc(self, new_layout) };
        }

        let new_layout = Layout::from_size_align(new_size, layout.align())
            .unwrap_or_else(|_| Layout::new::<u8>());

        // If new size fits in old allocation, return old pointer
        if new_size <= layout.size() {
            return ptr;
        }

        // Allocate new memory and copy
        let new_ptr = unsafe { core::alloc::GlobalAlloc::alloc(self, new_layout) };
        if !new_ptr.is_null() {
            core::ptr::copy_nonoverlapping(ptr, new_ptr, core::cmp::min(layout.size(), new_size));
            if let Some(ptr) = NonNull::new(ptr) {
                self.dealloc(ptr, layout);
            }
            new_ptr
        } else {
            core::ptr::null_mut()
        }
    }
}
