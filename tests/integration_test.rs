//! Integration tests for the buddy-slab-allocator crate.

extern crate buddy_slab_allocator;

use buddy_slab_allocator::{
    slab::SlabPageHeader, AllocError, BuddyAllocator, GlobalAllocator, OsImpl, SizeClass,
    SlabAllocResult, SlabAllocator, SlabDeallocResult,
};
use core::alloc::Layout;
use core::sync::atomic::{AtomicUsize, Ordering};
use std::alloc::{alloc, dealloc};

const PAGE_SIZE: usize = 0x1000;
const TEST_HEAP_SIZE: usize = 16 * 1024 * 1024; // 16 MiB

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

struct TestOs {
    cpu: AtomicUsize,
}

impl TestOs {
    const fn new() -> Self {
        Self {
            cpu: AtomicUsize::new(0),
        }
    }

    #[allow(dead_code)]
    fn set_cpu(&self, cpu: usize) {
        self.cpu.store(cpu, Ordering::Relaxed);
    }
}

impl OsImpl for TestOs {
    fn current_cpu_idx(&self) -> usize {
        self.cpu.load(Ordering::Relaxed)
    }
    fn virt_to_phys(&self, vaddr: usize) -> usize {
        vaddr // identity mapping
    }
}

static TEST_OS: TestOs = TestOs::new();

/// Allocate a region from the host allocator.
fn host_alloc(size: usize, align: usize) -> (*mut u8, Layout) {
    let layout = Layout::from_size_align(size, align).unwrap();
    let ptr = unsafe { alloc(layout) };
    assert!(!ptr.is_null(), "host alloc failed");
    (ptr, layout)
}

fn host_dealloc(ptr: *mut u8, layout: Layout) {
    unsafe { dealloc(ptr, layout) };
}

fn align_up(value: usize, align: usize) -> usize {
    (value + align - 1) & !(align - 1)
}

// ======================================================================
// Buddy allocator (standalone) tests
// ======================================================================

#[test]
fn buddy_basic_alloc_dealloc() {
    let (heap_ptr, heap_layout) = host_alloc(TEST_HEAP_SIZE, PAGE_SIZE);
    let heap_addr = heap_ptr as usize;
    let meta_size = BuddyAllocator::<PAGE_SIZE>::required_meta_size(TEST_HEAP_SIZE);
    let (meta_ptr, meta_layout) = host_alloc(meta_size, 16);

    let mut buddy = BuddyAllocator::<PAGE_SIZE>::new();
    unsafe {
        buddy
            .init(meta_ptr, meta_size, heap_addr, TEST_HEAP_SIZE, None)
            .unwrap();
    }

    let addr1 = buddy.alloc_pages(1, PAGE_SIZE).unwrap();
    assert!(addr1 >= heap_addr && addr1 < heap_addr + TEST_HEAP_SIZE);
    assert_eq!(addr1 % PAGE_SIZE, 0);

    let addr4 = buddy.alloc_pages(4, PAGE_SIZE).unwrap();
    assert_eq!(addr4 % PAGE_SIZE, 0);

    let free_before = buddy.free_pages();
    buddy.dealloc_pages(addr1, 1);
    buddy.dealloc_pages(addr4, 4);
    assert!(buddy.free_pages() > free_before);

    host_dealloc(meta_ptr, meta_layout);
    host_dealloc(heap_ptr, heap_layout);
}

#[test]
fn buddy_alignment() {
    // Heap must be aligned to the highest alignment we test (PAGE_SIZE * 4)
    // so that PFN-based alignment maps to absolute address alignment.
    let (heap_ptr, heap_layout) = host_alloc(TEST_HEAP_SIZE, PAGE_SIZE * 4);
    let heap_addr = heap_ptr as usize;
    let meta_size = BuddyAllocator::<PAGE_SIZE>::required_meta_size(TEST_HEAP_SIZE);
    let (meta_ptr, meta_layout) = host_alloc(meta_size, 16);

    let mut buddy = BuddyAllocator::<PAGE_SIZE>::new();
    unsafe {
        buddy
            .init(meta_ptr, meta_size, heap_addr, TEST_HEAP_SIZE, None)
            .unwrap();
    }

    let addr2 = buddy.alloc_pages(1, PAGE_SIZE * 2).unwrap();
    assert_eq!(addr2 % (PAGE_SIZE * 2), 0);

    let addr4 = buddy.alloc_pages(1, PAGE_SIZE * 4).unwrap();
    assert_eq!(addr4 % (PAGE_SIZE * 4), 0);

    buddy.dealloc_pages(addr2, 1);
    buddy.dealloc_pages(addr4, 1);

    host_dealloc(meta_ptr, meta_layout);
    host_dealloc(heap_ptr, heap_layout);
}

#[test]
fn buddy_aligned_alloc_dealloc_uses_recorded_order() {
    let heap_size = 64 * PAGE_SIZE;
    let (heap_ptr, heap_layout) = host_alloc(heap_size, PAGE_SIZE * 16);
    let heap_addr = heap_ptr as usize;
    let meta_size = BuddyAllocator::<PAGE_SIZE>::required_meta_size(heap_size);
    let (meta_ptr, meta_layout) = host_alloc(meta_size, 16);

    let mut buddy = BuddyAllocator::<PAGE_SIZE>::new();
    unsafe {
        buddy
            .init(meta_ptr, meta_size, heap_addr, heap_size, None)
            .unwrap();
    }

    let free_before = buddy.free_pages();
    let addr = buddy.alloc_pages(4, PAGE_SIZE * 16).unwrap();
    buddy.dealloc_pages(addr, 4);
    assert_eq!(buddy.free_pages(), free_before);

    host_dealloc(meta_ptr, meta_layout);
    host_dealloc(heap_ptr, heap_layout);
}

#[test]
fn buddy_exhaust_and_recover() {
    let heap_size = 64 * PAGE_SIZE; // Small heap
    let (heap_ptr, heap_layout) = host_alloc(heap_size, PAGE_SIZE);
    let heap_addr = heap_ptr as usize;
    let meta_size = BuddyAllocator::<PAGE_SIZE>::required_meta_size(heap_size);
    let (meta_ptr, meta_layout) = host_alloc(meta_size, 16);

    let mut buddy = BuddyAllocator::<PAGE_SIZE>::new();
    unsafe {
        buddy
            .init(meta_ptr, meta_size, heap_addr, heap_size, None)
            .unwrap();
    }

    let mut addrs = Vec::new();
    while let Ok(addr) = buddy.alloc_pages(1, PAGE_SIZE) {
        addrs.push(addr);
    }
    assert_eq!(buddy.free_pages(), 0);

    // Free half
    for addr in addrs.drain(..addrs.len() / 2) {
        buddy.dealloc_pages(addr, 1);
    }
    assert!(buddy.free_pages() > 0);

    // Allocate again
    let addr = buddy.alloc_pages(1, PAGE_SIZE);
    assert!(addr.is_ok());

    // Cleanup
    if let Ok(a) = addr {
        buddy.dealloc_pages(a, 1);
    }
    for a in addrs {
        buddy.dealloc_pages(a, 1);
    }

    host_dealloc(meta_ptr, meta_layout);
    host_dealloc(heap_ptr, heap_layout);
}

#[test]
fn buddy_merge_coalescing() {
    let heap_size = 16 * PAGE_SIZE;
    let (heap_ptr, heap_layout) = host_alloc(heap_size, PAGE_SIZE);
    let heap_addr = heap_ptr as usize;
    let meta_size = BuddyAllocator::<PAGE_SIZE>::required_meta_size(heap_size);
    let (meta_ptr, meta_layout) = host_alloc(meta_size, 16);

    let mut buddy = BuddyAllocator::<PAGE_SIZE>::new();
    unsafe {
        buddy
            .init(meta_ptr, meta_size, heap_addr, heap_size, None)
            .unwrap();
    }

    let initial_free = buddy.free_pages();

    // Allocate two single pages
    let a = buddy.alloc_pages(1, PAGE_SIZE).unwrap();
    let b = buddy.alloc_pages(1, PAGE_SIZE).unwrap();
    buddy.dealloc_pages(a, 1);
    buddy.dealloc_pages(b, 1);

    // After freeing both, free_pages should return to initial
    assert_eq!(buddy.free_pages(), initial_free);

    host_dealloc(meta_ptr, meta_layout);
    host_dealloc(heap_ptr, heap_layout);
}

// ======================================================================
// Slab allocator (standalone) tests
// ======================================================================

#[test]
fn slab_basic() {
    let (heap_ptr, heap_layout) = host_alloc(TEST_HEAP_SIZE, PAGE_SIZE);
    let heap_addr = heap_ptr as usize;
    let meta_size = BuddyAllocator::<PAGE_SIZE>::required_meta_size(TEST_HEAP_SIZE);
    let (meta_ptr, meta_layout) = host_alloc(meta_size, 16);

    let mut buddy = BuddyAllocator::<PAGE_SIZE>::new();
    unsafe {
        buddy
            .init(meta_ptr, meta_size, heap_addr, TEST_HEAP_SIZE, None)
            .unwrap();
    }

    let mut slab = SlabAllocator::<PAGE_SIZE>::new();

    let layout = Layout::from_size_align(64, 8).unwrap();
    // First alloc should request pages
    match slab.alloc(layout).unwrap() {
        SlabAllocResult::NeedsSlab { size_class, pages } => {
            let addr = buddy.alloc_pages(pages, PAGE_SIZE).unwrap();
            slab.add_slab(size_class, addr, pages * PAGE_SIZE, 0);
        }
        SlabAllocResult::Allocated(_) => panic!("should need slab first"),
    }

    // Now allocation should succeed
    let ptr = match slab.alloc(layout).unwrap() {
        SlabAllocResult::Allocated(p) => p,
        _ => panic!("expected allocated"),
    };

    // Dealloc
    match slab.dealloc(ptr, layout) {
        SlabDeallocResult::Done => {}
        SlabDeallocResult::FreeSlab { .. } => {} // also valid
    }

    host_dealloc(meta_ptr, meta_layout);
    host_dealloc(heap_ptr, heap_layout);
}

#[test]
fn slab_many_objects() {
    let (heap_ptr, heap_layout) = host_alloc(TEST_HEAP_SIZE, PAGE_SIZE * 4);
    let heap_addr = heap_ptr as usize;
    let meta_size = BuddyAllocator::<PAGE_SIZE>::required_meta_size(TEST_HEAP_SIZE);
    let (meta_ptr, meta_layout) = host_alloc(meta_size, 16);

    let mut buddy = BuddyAllocator::<PAGE_SIZE>::new();
    unsafe {
        buddy
            .init(meta_ptr, meta_size, heap_addr, TEST_HEAP_SIZE, None)
            .unwrap();
    }

    let mut slab = SlabAllocator::<PAGE_SIZE>::new();
    let layout = Layout::from_size_align(32, 8).unwrap();

    let mut ptrs = Vec::new();
    for _ in 0..200 {
        loop {
            match slab.alloc(layout).unwrap() {
                SlabAllocResult::Allocated(p) => {
                    ptrs.push(p);
                    break;
                }
                SlabAllocResult::NeedsSlab { size_class, pages } => {
                    let slab_bytes = pages * PAGE_SIZE;
                    let addr = buddy.alloc_pages(pages, slab_bytes).unwrap();
                    slab.add_slab(size_class, addr, slab_bytes, 0);
                }
            }
        }
    }

    assert_eq!(ptrs.len(), 200);
    for ptr in ptrs {
        let _ = slab.dealloc(ptr, layout);
    }

    host_dealloc(meta_ptr, meta_layout);
    host_dealloc(heap_ptr, heap_layout);
}

#[test]
fn slab_all_size_classes() {
    let (heap_ptr, heap_layout) = host_alloc(TEST_HEAP_SIZE, PAGE_SIZE * 4);
    let heap_addr = heap_ptr as usize;
    let meta_size = BuddyAllocator::<PAGE_SIZE>::required_meta_size(TEST_HEAP_SIZE);
    let (meta_ptr, meta_layout) = host_alloc(meta_size, 16);

    let mut buddy = BuddyAllocator::<PAGE_SIZE>::new();
    unsafe {
        buddy
            .init(meta_ptr, meta_size, heap_addr, TEST_HEAP_SIZE, None)
            .unwrap();
    }

    let mut slab = SlabAllocator::<PAGE_SIZE>::new();
    let mut allocations = Vec::new();

    for sc in SizeClass::ALL {
        let layout = Layout::from_size_align(sc.size(), sc.size()).unwrap();
        loop {
            match slab.alloc(layout).unwrap() {
                SlabAllocResult::Allocated(p) => {
                    allocations.push((p, layout));
                    break;
                }
                SlabAllocResult::NeedsSlab { size_class, pages } => {
                    let slab_bytes = pages * PAGE_SIZE;
                    let addr = buddy.alloc_pages(pages, slab_bytes).unwrap();
                    slab.add_slab(size_class, addr, slab_bytes, 0);
                }
            }
        }
    }

    assert_eq!(allocations.len(), SizeClass::COUNT);
    for (ptr, layout) in allocations {
        let _ = slab.dealloc(ptr, layout);
    }

    host_dealloc(meta_ptr, meta_layout);
    host_dealloc(heap_ptr, heap_layout);
}

// ======================================================================
// Global allocator tests
// ======================================================================

fn init_global(allocator: &GlobalAllocator<PAGE_SIZE>, region: &mut [u8], cpu_count: usize) {
    unsafe { allocator.init(region, cpu_count, &TEST_OS).unwrap() };
}

#[test]
fn global_page_alloc() {
    let (region_ptr, region_layout) = host_alloc(TEST_HEAP_SIZE, PAGE_SIZE * 4);
    let region_addr = region_ptr as usize;
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let region = unsafe { core::slice::from_raw_parts_mut(region_ptr, TEST_HEAP_SIZE) };
    init_global(&allocator, region, 1);

    let managed_start = allocator.managed_heap_start();
    let managed_end = managed_start + allocator.managed_heap_size();

    let addr = allocator.alloc_pages(4, PAGE_SIZE).unwrap();
    assert!(managed_start > region_addr);
    assert!(addr >= managed_start && addr < managed_end);
    assert_eq!(addr % PAGE_SIZE, 0);
    allocator.dealloc_pages(addr, 4);

    host_dealloc(region_ptr, region_layout);
}

#[test]
fn global_small_alloc() {
    let (region_ptr, region_layout) = host_alloc(TEST_HEAP_SIZE, PAGE_SIZE * 4);
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let region = unsafe { core::slice::from_raw_parts_mut(region_ptr, TEST_HEAP_SIZE) };
    init_global(&allocator, region, 1);

    let layout = Layout::from_size_align(64, 8).unwrap();
    let ptr = allocator.alloc(layout).unwrap();
    unsafe { allocator.dealloc(ptr, layout) };

    host_dealloc(region_ptr, region_layout);
}

#[test]
fn global_large_alloc() {
    let (region_ptr, region_layout) = host_alloc(TEST_HEAP_SIZE, PAGE_SIZE * 4);
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let region = unsafe { core::slice::from_raw_parts_mut(region_ptr, TEST_HEAP_SIZE) };
    init_global(&allocator, region, 1);

    let layout = Layout::from_size_align(8192, PAGE_SIZE).unwrap();
    let ptr = allocator.alloc(layout).unwrap();
    unsafe { allocator.dealloc(ptr, layout) };

    host_dealloc(region_ptr, region_layout);
}

#[test]
fn global_mixed_alloc() {
    let (region_ptr, region_layout) = host_alloc(TEST_HEAP_SIZE, PAGE_SIZE * 4);
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let region = unsafe { core::slice::from_raw_parts_mut(region_ptr, TEST_HEAP_SIZE) };
    init_global(&allocator, region, 1);

    let sizes: &[(usize, usize)] = &[
        (8, 8),
        (64, 8),
        (1024, 8),
        (4096, PAGE_SIZE),
        (8192, PAGE_SIZE),
    ];
    let mut allocations = Vec::new();
    for &(size, align) in sizes {
        let layout = Layout::from_size_align(size, align).unwrap();
        let ptr = allocator.alloc(layout).unwrap();
        allocations.push((ptr, layout));
    }
    for (ptr, layout) in allocations {
        unsafe { allocator.dealloc(ptr, layout) };
    }

    host_dealloc(region_ptr, region_layout);
}

#[test]
fn global_cross_cpu_free() {
    let (region_ptr, region_layout) = host_alloc(TEST_HEAP_SIZE, PAGE_SIZE * 4);
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let region = unsafe { core::slice::from_raw_parts_mut(region_ptr, TEST_HEAP_SIZE) };
    init_global(&allocator, region, 2);

    // Allocate on CPU 0
    TEST_OS.set_cpu(0);
    let layout = Layout::from_size_align(64, 8).unwrap();
    let mut ptrs = Vec::new();
    for _ in 0..10 {
        ptrs.push(allocator.alloc(layout).unwrap());
    }

    // Free from CPU 1 (triggers remote free path)
    TEST_OS.set_cpu(1);
    for ptr in ptrs {
        unsafe { allocator.dealloc(ptr, layout) };
    }

    // Allocate on CPU 0 again — should drain remote frees and succeed
    TEST_OS.set_cpu(0);
    let ptr = allocator.alloc(layout).unwrap();
    unsafe { allocator.dealloc(ptr, layout) };

    host_dealloc(region_ptr, region_layout);
}

#[test]
fn global_cross_cpu_free_drains_remote_queue() {
    let (region_ptr, region_layout) = host_alloc(TEST_HEAP_SIZE, PAGE_SIZE * 4);
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let region = unsafe { core::slice::from_raw_parts_mut(region_ptr, TEST_HEAP_SIZE) };
    init_global(&allocator, region, 2);

    TEST_OS.set_cpu(0);
    let layout = Layout::from_size_align(64, 8).unwrap();
    let ptr = allocator.alloc(layout).unwrap();

    let slab_bytes = SizeClass::from_layout(layout)
        .unwrap()
        .slab_pages(PAGE_SIZE)
        * PAGE_SIZE;
    let base = SlabPageHeader::base_from_obj_addr::<PAGE_SIZE>(ptr.as_ptr() as usize, slab_bytes);
    let hdr = unsafe { &*(base as *const SlabPageHeader) };
    assert_eq!(hdr.owner_cpu, 0);
    assert_eq!(hdr.remote_free_count.load(Ordering::Relaxed), 0);

    TEST_OS.set_cpu(1);
    unsafe { allocator.dealloc(ptr, layout) };
    assert_eq!(hdr.remote_free_count.load(Ordering::Relaxed), 1);
    assert_ne!(hdr.remote_free_head.load(Ordering::Relaxed), 0);

    TEST_OS.set_cpu(0);
    let ptr2 = allocator.alloc(layout).unwrap();
    assert_eq!(hdr.remote_free_count.load(Ordering::Relaxed), 0);
    assert_eq!(hdr.remote_free_head.load(Ordering::Relaxed), 0);
    unsafe { allocator.dealloc(ptr2, layout) };

    host_dealloc(region_ptr, region_layout);
}

#[test]
fn global_cross_cpu_free_multiple_rounds_same_slab() {
    let (region_ptr, region_layout) = host_alloc(TEST_HEAP_SIZE, PAGE_SIZE * 4);
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let region = unsafe { core::slice::from_raw_parts_mut(region_ptr, TEST_HEAP_SIZE) };
    init_global(&allocator, region, 2);

    let layout = Layout::from_size_align(64, 8).unwrap();

    TEST_OS.set_cpu(0);
    let first = allocator.alloc(layout).unwrap();
    let slab_bytes = SizeClass::from_layout(layout)
        .unwrap()
        .slab_pages(PAGE_SIZE)
        * PAGE_SIZE;
    let base = SlabPageHeader::base_from_obj_addr::<PAGE_SIZE>(first.as_ptr() as usize, slab_bytes);
    let hdr = unsafe { &*(base as *const SlabPageHeader) };
    let object_count = hdr.object_count as usize;
    let mut ptrs = Vec::with_capacity(object_count);
    ptrs.push(first);
    for _ in 1..object_count {
        let ptr = allocator.alloc(layout).unwrap();
        let ptr_base =
            SlabPageHeader::base_from_obj_addr::<PAGE_SIZE>(ptr.as_ptr() as usize, slab_bytes);
        assert_eq!(ptr_base, base);
        ptrs.push(ptr);
    }

    TEST_OS.set_cpu(1);
    for &ptr in &ptrs {
        unsafe { allocator.dealloc(ptr, layout) };
    }
    assert_eq!(
        hdr.remote_free_count.load(Ordering::Relaxed) as usize,
        object_count
    );

    TEST_OS.set_cpu(0);
    let mut drained = Vec::with_capacity(object_count);
    for _ in 0..object_count {
        drained.push(allocator.alloc(layout).unwrap());
    }
    assert_eq!(hdr.remote_free_count.load(Ordering::Relaxed), 0);
    assert_eq!(hdr.remote_free_head.load(Ordering::Relaxed), 0);

    for ptr in drained {
        unsafe { allocator.dealloc(ptr, layout) };
    }

    host_dealloc(region_ptr, region_layout);
}

#[test]
fn global_lowmem_pages() {
    // Use a custom OsImpl that maps virt addresses below 4 GiB so lowmem
    // allocation can succeed on 64-bit hosts where heap addresses are > 4 GiB.
    struct LowmemOs;
    impl OsImpl for LowmemOs {
        fn current_cpu_idx(&self) -> usize {
            0
        }
        fn virt_to_phys(&self, vaddr: usize) -> usize {
            vaddr & 0x0FFF_FFFF
        }
    }
    static LOWMEM_OS: LowmemOs = LowmemOs;

    let (region_ptr, region_layout) = host_alloc(TEST_HEAP_SIZE, PAGE_SIZE * 4);
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let region = unsafe { core::slice::from_raw_parts_mut(region_ptr, TEST_HEAP_SIZE) };
    unsafe { allocator.init(region, 1, &LOWMEM_OS).unwrap() };

    let addr = allocator.alloc_pages_lowmem(1, PAGE_SIZE).unwrap();
    assert!(addr >= allocator.managed_heap_start());
    allocator.dealloc_pages(addr, 1);

    host_dealloc(region_ptr, region_layout);
}

#[test]
fn global_unaligned_region_start() {
    let (region_ptr, region_layout) = host_alloc(TEST_HEAP_SIZE + PAGE_SIZE, PAGE_SIZE * 4);
    let region_start = region_ptr as usize + 1;
    let region_size = TEST_HEAP_SIZE;
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let region =
        unsafe { core::slice::from_raw_parts_mut(region_ptr.wrapping_add(1), region_size) };
    init_global(&allocator, region, 1);

    let managed_start = allocator.managed_heap_start();
    let managed_end = managed_start + allocator.managed_heap_size();

    assert_eq!(managed_start % PAGE_SIZE, 0);
    assert!(managed_start >= region_start);
    assert!(managed_end <= region_start + region_size);

    let addr = allocator.alloc_pages(1, PAGE_SIZE).unwrap();
    assert!(addr >= managed_start && addr < managed_end);
    allocator.dealloc_pages(addr, 1);

    host_dealloc(region_ptr, region_layout);
}

#[test]
fn global_rejects_region_without_one_managed_page() {
    let buddy_meta_size = BuddyAllocator::<PAGE_SIZE>::required_meta_size(PAGE_SIZE);
    let slab_align = core::mem::align_of::<spin::Mutex<SlabAllocator<PAGE_SIZE>>>();
    let slab_offset = align_up(buddy_meta_size, slab_align);
    let slab_size = core::mem::size_of::<spin::Mutex<SlabAllocator<PAGE_SIZE>>>();
    let region_size = PAGE_SIZE + slab_offset + slab_size - 1;
    let (region_ptr, region_layout) = host_alloc(region_size, PAGE_SIZE);
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let region = unsafe { core::slice::from_raw_parts_mut(region_ptr, region_size) };

    let err = unsafe { allocator.init(region, 1, &TEST_OS) }.unwrap_err();
    assert_eq!(err, AllocError::InvalidParam);

    host_dealloc(region_ptr, region_layout);
}
