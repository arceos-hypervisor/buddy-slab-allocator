//! Buddy page allocator — page-metadata-based with intrusive free lists.
//!
//! The allocator manages one or more contiguous virtual address ranges ("sections").
//! Each section stores its own [`BuddySection`] descriptor and [`PageMeta`] array
//! in the caller-provided region prefix, enabling O(1) free-list operations
//! without any dynamic allocation.

pub mod page_meta;

pub use page_meta::{PageFlags, PageMeta, PFN_NONE};

use core::ptr;

use crate::error::{AllocError, AllocResult};
use crate::{align_up, is_aligned, OsImpl};
use page_meta::{free_list_pop, free_list_push, free_list_remove};

/// Maximum buddy order. With 4 KiB pages this gives 2^20 × 4 KiB = 4 GiB blocks.
pub const MAX_ORDER: usize = 20;

/// DMA32 zone upper bound (4 GiB physical).
const DMA32_LIMIT: usize = 0x1_0000_0000;

struct RegionLayout {
    section_start: usize,
    meta_start: usize,
    managed_heap_start: usize,
    managed_heap_size: usize,
}

pub(crate) struct SectionInitSpec {
    pub(crate) region_start: usize,
    pub(crate) region_size: usize,
    pub(crate) section_ptr: *mut BuddySection,
    pub(crate) meta_ptr: *mut u8,
    pub(crate) meta_size: usize,
    pub(crate) heap_start: usize,
    pub(crate) heap_size: usize,
}

/// Public read-only summary of a managed section.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ManagedSection {
    pub start: usize,
    pub size: usize,
    pub free_pages: usize,
    pub total_pages: usize,
}

/// Per-region buddy state stored in the region prefix.
#[repr(C)]
pub(crate) struct BuddySection {
    pub(crate) next: *mut BuddySection,
    pub(crate) region_start: usize,
    pub(crate) region_size: usize,
    pub(crate) meta: *mut PageMeta,
    pub(crate) max_pages: usize,
    pub(crate) heap_start: usize,
    pub(crate) heap_size: usize,
    pub(crate) free_lists: [u32; MAX_ORDER + 1],
    pub(crate) free_pages: usize,
    pub(crate) total_pages: usize,
}

impl BuddySection {
    const fn metadata_align() -> usize {
        let section_align = core::mem::align_of::<BuddySection>();
        let meta_align = core::mem::align_of::<PageMeta>();
        if section_align > meta_align {
            section_align
        } else {
            meta_align
        }
    }

    fn metadata_layout_for_pages(pages: usize) -> Option<(usize, usize)> {
        let meta_offset = align_up(
            core::mem::size_of::<BuddySection>(),
            core::mem::align_of::<PageMeta>(),
        );
        let page_meta_size = pages.checked_mul(core::mem::size_of::<PageMeta>())?;
        let meta_size = meta_offset.checked_add(page_meta_size)?;
        Some((meta_offset, meta_size))
    }

    fn available_heap_pages<const PAGE_SIZE: usize>(
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

    fn can_manage_pages<const PAGE_SIZE: usize>(
        region_end: usize,
        section_start: usize,
        pages: usize,
    ) -> bool {
        let Some((_, meta_size)) = Self::metadata_layout_for_pages(pages) else {
            return false;
        };
        let Some(available_pages) =
            Self::available_heap_pages::<PAGE_SIZE>(region_end, section_start, meta_size)
        else {
            return false;
        };
        available_pages >= pages
    }

    fn compute_region_layout<const PAGE_SIZE: usize>(
        region_start: usize,
        region_size: usize,
    ) -> Option<RegionLayout> {
        if region_size == 0 || !PAGE_SIZE.is_power_of_two() {
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
            if Self::can_manage_pages::<PAGE_SIZE>(region_end, section_start, mid) {
                low = mid;
            } else {
                high = mid - 1;
            }
        }

        if low == 0 {
            return None;
        }

        let (meta_offset, meta_size) = Self::metadata_layout_for_pages(low)?;
        let meta_start = section_start.checked_add(meta_offset)?;
        let managed_heap_start = align_up(section_start.checked_add(meta_size)?, PAGE_SIZE);
        let managed_heap_size = low.checked_mul(PAGE_SIZE)?;

        Some(RegionLayout {
            section_start,
            meta_start,
            managed_heap_start,
            managed_heap_size,
        })
    }

    unsafe fn init_at<const PAGE_SIZE: usize>(
        section_ptr: *mut BuddySection,
        region_start: usize,
        region_size: usize,
        meta_ptr: *mut u8,
        meta_size: usize,
        heap_start: usize,
        heap_size: usize,
    ) -> AllocResult {
        if !PAGE_SIZE.is_power_of_two() {
            return Err(AllocError::InvalidParam);
        }
        if !is_aligned(heap_start, PAGE_SIZE) || heap_size == 0 {
            return Err(AllocError::InvalidParam);
        }

        let total_pages = heap_size / PAGE_SIZE;
        let required = BuddyAllocator::<PAGE_SIZE>::required_meta_size(heap_size);
        if meta_size < required {
            return Err(AllocError::InvalidParam);
        }

        let meta = meta_ptr as *mut PageMeta;
        for i in 0..total_pages {
            meta.add(i).write(PageMeta::new());
        }

        section_ptr.write(BuddySection {
            next: ptr::null_mut(),
            region_start,
            region_size,
            meta,
            max_pages: total_pages,
            heap_start,
            heap_size,
            free_lists: [PFN_NONE; MAX_ORDER + 1],
            free_pages: 0,
            total_pages,
        });

        let section = &mut *section_ptr;
        let mut pfn: usize = 0;
        while pfn < total_pages {
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
            let m = &mut *section.meta.add(pfn);
            m.flags = PageFlags::Free;
            m.order = order as u8;
            free_list_push(section.meta, &mut section.free_lists, pfn as u32, order);
            section.free_pages += block_pages;
            pfn += block_pages;
        }

        Ok(())
    }

    #[inline]
    fn contains_heap_addr(&self, addr: usize) -> bool {
        addr >= self.heap_start && addr < self.heap_start + self.heap_size
    }

    #[inline]
    fn summary(&self) -> ManagedSection {
        ManagedSection {
            start: self.heap_start,
            size: self.heap_size,
            free_pages: self.free_pages,
            total_pages: self.total_pages,
        }
    }
}

/// Page-metadata-based buddy allocator.
///
/// `PAGE_SIZE` must be a power of two (commonly 0x1000 = 4 KiB).
pub struct BuddyAllocator<const PAGE_SIZE: usize = 0x1000> {
    sections_head: *mut BuddySection,
    sections_tail: *mut BuddySection,
    section_count: usize,
    os: Option<&'static dyn OsImpl>,
}

// SAFETY: The allocator is designed to be wrapped in a SpinMutex.
// All section pointers point into caller-provided regions whose lifetime is managed externally.
unsafe impl<const PAGE_SIZE: usize> Send for BuddyAllocator<PAGE_SIZE> {}

impl<const PAGE_SIZE: usize> BuddyAllocator<PAGE_SIZE> {
    /// Calculate the metadata-region size (in bytes) required for `heap_size` bytes.
    pub const fn required_meta_size(heap_size: usize) -> usize {
        let pages = heap_size / PAGE_SIZE;
        pages * core::mem::size_of::<PageMeta>()
    }

    /// Create an uninitialised allocator. Call [`init`](Self::init) before use.
    pub const fn new() -> Self {
        Self {
            sections_head: ptr::null_mut(),
            sections_tail: ptr::null_mut(),
            section_count: 0,
            os: None,
        }
    }
}

impl<const PAGE_SIZE: usize> Default for BuddyAllocator<PAGE_SIZE> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const PAGE_SIZE: usize> BuddyAllocator<PAGE_SIZE> {
    pub(crate) fn reset(&mut self, os: Option<&'static dyn OsImpl>) {
        self.sections_head = ptr::null_mut();
        self.sections_tail = ptr::null_mut();
        self.section_count = 0;
        self.os = os;
    }

    /// Initialise the allocator over the first section.
    ///
    /// # Safety
    /// - `region` must be writable and remain valid for the lifetime of this allocator.
    /// - Bytes consumed by metadata become unavailable for allocation.
    pub unsafe fn init(
        &mut self,
        region: &mut [u8],
        os: Option<&'static dyn OsImpl>,
    ) -> AllocResult {
        self.reset(os);
        self.add_region(region)
    }

    /// Add a new managed region after initialisation.
    ///
    /// # Safety
    /// - `region` must be writable and remain valid for the lifetime of this allocator.
    /// - The region must not overlap any existing managed region.
    pub unsafe fn add_region(&mut self, region: &mut [u8]) -> AllocResult {
        let region_start = region.as_mut_ptr() as usize;
        let region_size = region.len();
        let layout = BuddySection::compute_region_layout::<PAGE_SIZE>(region_start, region_size)
            .ok_or(AllocError::InvalidParam)?;
        self.add_region_raw(SectionInitSpec {
            region_start,
            region_size,
            section_ptr: layout.section_start as *mut BuddySection,
            meta_ptr: layout.meta_start as *mut u8,
            meta_size: Self::required_meta_size(layout.managed_heap_size),
            heap_start: layout.managed_heap_start,
            heap_size: layout.managed_heap_size,
        })
    }

    pub(crate) unsafe fn add_region_raw(&mut self, spec: SectionInitSpec) -> AllocResult {
        let region_size = spec.region_size;
        let region_end = spec
            .region_start
            .checked_add(region_size)
            .ok_or(AllocError::InvalidParam)?;
        let heap_end = spec
            .heap_start
            .checked_add(spec.heap_size)
            .ok_or(AllocError::InvalidParam)?;
        if heap_end > region_end {
            return Err(AllocError::InvalidParam);
        }

        let mut section = self.sections_head;
        while !section.is_null() {
            let existing = &*section;
            let existing_end = existing
                .region_start
                .checked_add(existing.region_size)
                .ok_or(AllocError::InvalidParam)?;
            if spec.region_start < existing_end && existing.region_start < region_end {
                return Err(AllocError::MemoryOverlap);
            }
            section = existing.next;
        }

        BuddySection::init_at::<PAGE_SIZE>(
            spec.section_ptr,
            spec.region_start,
            spec.region_size,
            spec.meta_ptr,
            spec.meta_size,
            spec.heap_start,
            spec.heap_size,
        )?;

        if self.sections_head.is_null() {
            self.sections_head = spec.section_ptr;
        } else {
            (*self.sections_tail).next = spec.section_ptr;
        }
        self.sections_tail = spec.section_ptr;
        self.section_count += 1;

        log::debug!(
            "BuddyAllocator: add section region {:#x}+{:#x}, heap {:#x}..{:#x}, {} pages",
            spec.region_start,
            spec.region_size,
            spec.heap_start,
            heap_end,
            spec.heap_size / PAGE_SIZE,
        );

        Ok(())
    }

    /// Number of managed sections.
    pub fn section_count(&self) -> usize {
        self.section_count
    }

    /// Read-only summary for a managed section by registration order.
    pub fn section(&self, index: usize) -> Option<ManagedSection> {
        let mut current = self.sections_head;
        let mut i = 0usize;
        while !current.is_null() {
            if i == index {
                return Some(unsafe { (&*current).summary() });
            }
            current = unsafe { (*current).next };
            i += 1;
        }
        None
    }

    /// Total number of pages managed across all sections.
    pub fn total_pages(&self) -> usize {
        let mut total = 0usize;
        let mut current = self.sections_head;
        while !current.is_null() {
            total += unsafe { (*current).total_pages };
            current = unsafe { (*current).next };
        }
        total
    }

    /// Total managed heap bytes across all sections.
    ///
    /// This counts only bytes in allocatable heaps, excluding region-prefix metadata.
    pub fn managed_bytes(&self) -> usize {
        let mut total = 0usize;
        let mut current = self.sections_head;
        while !current.is_null() {
            total += unsafe { (*current).heap_size };
            current = unsafe { (*current).next };
        }
        total
    }

    /// Number of currently free pages across all sections.
    pub fn free_pages(&self) -> usize {
        let mut total = 0usize;
        let mut current = self.sections_head;
        while !current.is_null() {
            total += unsafe { (*current).free_pages };
            current = unsafe { (*current).next };
        }
        total
    }

    /// Allocated backend bytes across all sections.
    ///
    /// This is computed as managed heap bytes minus currently free page bytes.
    /// It reflects page-level occupancy, so it includes slab pages, alignment
    /// amplification, and internal fragmentation.
    pub fn allocated_bytes(&self) -> usize {
        self.managed_bytes()
            .saturating_sub(self.free_pages().saturating_mul(PAGE_SIZE))
    }

    /// Allocate `count` contiguous pages, returning the virtual address.
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

        let align_order = (align / PAGE_SIZE).trailing_zeros() as usize;
        let effective_order = order.max(align_order);

        let mut section = self.sections_head;
        while !section.is_null() {
            if let Ok(addr) = unsafe { Self::alloc_from_section(&mut *section, effective_order) } {
                return Ok(addr);
            }
            section = unsafe { (*section).next };
        }

        Err(AllocError::NoMemory)
    }

    fn alloc_from_section(section: &mut BuddySection, order: usize) -> AllocResult<usize> {
        let mut found_order = order;
        while found_order <= MAX_ORDER {
            if section.free_lists[found_order] != PFN_NONE {
                break;
            }
            found_order += 1;
        }
        if found_order > MAX_ORDER {
            return Err(AllocError::NoMemory);
        }

        let pfn = unsafe { free_list_pop(section.meta, &mut section.free_lists, found_order) };
        debug_assert_ne!(pfn, PFN_NONE);

        let mut current_order = found_order;
        while current_order > order {
            current_order -= 1;
            let buddy_pfn = pfn as usize + (1 << current_order);
            unsafe {
                let bm = &mut *section.meta.add(buddy_pfn);
                bm.flags = PageFlags::Free;
                bm.order = current_order as u8;
                free_list_push(
                    section.meta,
                    &mut section.free_lists,
                    buddy_pfn as u32,
                    current_order,
                );
            }
        }

        unsafe {
            let m = &mut *section.meta.add(pfn as usize);
            m.flags = PageFlags::Allocated;
            m.order = order as u8;
        }

        section.free_pages -= 1 << order;
        Ok(section.heap_start + (pfn as usize) * PAGE_SIZE)
    }

    /// Allocate pages whose *physical* address is below 4 GiB (DMA32 zone).
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

        let mut section = self.sections_head;
        while !section.is_null() {
            if let Ok(addr) =
                unsafe { Self::alloc_lowmem_from_section(&mut *section, effective_order, os) }
            {
                return Ok(addr);
            }
            section = unsafe { (*section).next };
        }

        Err(AllocError::NoMemory)
    }

    fn alloc_lowmem_from_section(
        section: &mut BuddySection,
        effective_order: usize,
        os: &'static dyn OsImpl,
    ) -> AllocResult<usize> {
        for search_order in effective_order..=MAX_ORDER {
            let mut pfn_u32 = section.free_lists[search_order];
            while pfn_u32 != PFN_NONE {
                let addr = section.heap_start + (pfn_u32 as usize) * PAGE_SIZE;
                let phys = os.virt_to_phys(addr);
                let block_bytes = (1usize << search_order) * PAGE_SIZE;
                if phys + block_bytes <= DMA32_LIMIT {
                    unsafe {
                        free_list_remove(
                            section.meta,
                            &mut section.free_lists,
                            pfn_u32,
                            search_order,
                        );
                    }

                    let mut current_order = search_order;
                    while current_order > effective_order {
                        current_order -= 1;
                        let buddy_pfn = pfn_u32 as usize + (1 << current_order);
                        unsafe {
                            let bm = &mut *section.meta.add(buddy_pfn);
                            bm.flags = PageFlags::Free;
                            bm.order = current_order as u8;
                            free_list_push(
                                section.meta,
                                &mut section.free_lists,
                                buddy_pfn as u32,
                                current_order,
                            );
                        }
                    }

                    unsafe {
                        let m = &mut *section.meta.add(pfn_u32 as usize);
                        m.flags = PageFlags::Allocated;
                        m.order = effective_order as u8;
                    }
                    section.free_pages -= 1 << effective_order;
                    return Ok(addr);
                }
                pfn_u32 = unsafe { (*section.meta.add(pfn_u32 as usize)).next };
            }
        }

        Err(AllocError::NoMemory)
    }

    /// Free pages previously obtained via [`alloc_pages`](Self::alloc_pages).
    ///
    /// `addr` must be the exact address returned by alloc. The allocator frees
    /// the full block size recorded in page metadata, which may be larger than
    /// `count` if the original allocation was rounded up for buddy order or alignment.
    pub fn dealloc_pages(&mut self, addr: usize, count: usize) {
        let Some(section) = self.find_section_by_addr_mut(addr) else {
            debug_assert!(
                false,
                "dealloc_pages called with address outside all sections"
            );
            return;
        };

        debug_assert!(is_aligned(addr, PAGE_SIZE));
        debug_assert!(count > 0);

        let pfn = (addr - section.heap_start) / PAGE_SIZE;
        debug_assert!(pfn < section.max_pages);
        let stored = unsafe { &*section.meta.add(pfn) };
        debug_assert!(
            stored.flags == PageFlags::Allocated || stored.flags == PageFlags::Slab,
            "dealloc_pages called on non-allocated block"
        );

        let expected_order = count.next_power_of_two().trailing_zeros() as usize;
        let order = stored.order as usize;
        debug_assert!(
            expected_order <= order,
            "dealloc_pages count implies larger order than the allocated block"
        );
        Self::dealloc_in_section(section, pfn, order);
    }

    /// Mark the page at `addr` with the given flags (used by slab to tag pages).
    ///
    /// # Safety
    /// The caller must ensure `addr` is valid and properly allocated.
    pub unsafe fn set_page_flags(&mut self, addr: usize, flags: PageFlags) -> AllocResult {
        let section = self
            .find_section_by_addr_mut(addr)
            .ok_or(AllocError::NotFound)?;
        let pfn = (addr - section.heap_start) / PAGE_SIZE;
        (*section.meta.add(pfn)).flags = flags;
        Ok(())
    }

    /// Read the flags of the page containing `addr`.
    pub fn page_flags(&self, addr: usize) -> AllocResult<PageFlags> {
        let section = self
            .find_section_by_addr(addr)
            .ok_or(AllocError::NotFound)?;
        let pfn = (addr - section.heap_start) / PAGE_SIZE;
        Ok(unsafe { (*section.meta.add(pfn)).flags })
    }

    fn dealloc_in_section(section: &mut BuddySection, mut pfn: usize, mut order: usize) {
        let freed_pages = 1usize << order;

        while order < MAX_ORDER {
            let buddy_pfn = pfn ^ (1 << order);
            if buddy_pfn >= section.max_pages {
                break;
            }
            let buddy = unsafe { &*section.meta.add(buddy_pfn) };
            if buddy.flags != PageFlags::Free || buddy.order as usize != order {
                break;
            }
            unsafe {
                free_list_remove(
                    section.meta,
                    &mut section.free_lists,
                    buddy_pfn as u32,
                    order,
                );
            }
            pfn = pfn.min(buddy_pfn);
            order += 1;
        }

        unsafe {
            let m = &mut *section.meta.add(pfn);
            m.flags = PageFlags::Free;
            m.order = order as u8;
            free_list_push(section.meta, &mut section.free_lists, pfn as u32, order);
        }
        section.free_pages += freed_pages;
    }

    fn find_section_by_addr(&self, addr: usize) -> Option<&BuddySection> {
        let mut section = self.sections_head;
        while !section.is_null() {
            let current = unsafe { &*section };
            if current.contains_heap_addr(addr) {
                return Some(current);
            }
            section = current.next;
        }
        None
    }

    fn find_section_by_addr_mut(&mut self, addr: usize) -> Option<&mut BuddySection> {
        let mut section = self.sections_head;
        while !section.is_null() {
            let current = unsafe { &mut *section };
            if current.contains_heap_addr(addr) {
                return Some(current);
            }
            section = current.next;
        }
        None
    }
}
