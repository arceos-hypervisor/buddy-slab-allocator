//! Integration tests for the allocator crate.

#![no_std]

extern crate alloc;
extern crate buddy_slab_allocator;

use alloc::vec::Vec;
use buddy_slab_allocator::{
    AllocError, CompositePageAllocator, GlobalAllocator, Os, SlabAllocDecision, SlabByteAllocator,
    SlabDeallocDecision,
};
use core::alloc::Layout;
use core::sync::atomic::{AtomicUsize, Ordering};

const PAGE_SIZE: usize = 0x1000;
const TEST_HEAP_SIZE: usize = 16 * 1024 * 1024;

struct MockOs {
    cpu: AtomicUsize,
}

impl MockOs {
    const fn new() -> Self {
        Self {
            cpu: AtomicUsize::new(0),
        }
    }

    fn set_cpu(&self, cpu: usize) {
        self.cpu.store(cpu, Ordering::Relaxed);
    }
}

impl Os for MockOs {
    fn current_cpu_idx(&self) -> usize {
        self.cpu.load(Ordering::Relaxed)
    }
}

struct FixedOs;

impl Os for FixedOs {
    fn current_cpu_idx(&self) -> usize {
        0
    }
}

static FIXED_OS: FixedOs = FixedOs;
static SWITCHING_OS: MockOs = MockOs::new();

fn alloc_region(size: usize, align: usize) -> (*mut u8, Layout) {
    let layout = Layout::from_size_align(size, align).unwrap();
    let ptr = unsafe { alloc::alloc::alloc(layout) };
    assert!(!ptr.is_null(), "Failed to allocate test region");
    (ptr, layout)
}

fn dealloc_region(ptr: *mut u8, layout: Layout) {
    unsafe { alloc::alloc::dealloc(ptr, layout) };
}

fn alloc_test_heap(size: usize) -> (*mut u8, Layout) {
    alloc_region(size, PAGE_SIZE)
}

fn alloc_metadata(cpu_count: usize) -> (*mut u8, Layout) {
    alloc_region(
        GlobalAllocator::<PAGE_SIZE>::required_metadata_size(cpu_count),
        PAGE_SIZE,
    )
}

fn init_global_allocator(
    allocator: &mut GlobalAllocator<PAGE_SIZE>,
    heap_addr: usize,
    heap_size: usize,
    cpu_count: usize,
) -> (*mut u8, Layout) {
    let (meta_ptr, meta_layout) = alloc_metadata(cpu_count);
    unsafe {
        allocator
            .init(
                meta_ptr as usize,
                meta_layout.size(),
                heap_addr,
                heap_size,
                cpu_count,
                &FIXED_OS,
            )
            .unwrap();
    }
    (meta_ptr, meta_layout)
}

fn init_global_allocator_with_os(
    allocator: &mut GlobalAllocator<PAGE_SIZE>,
    heap_addr: usize,
    heap_size: usize,
    cpu_count: usize,
    os: &'static dyn Os,
) -> (*mut u8, Layout) {
    let (meta_ptr, meta_layout) = alloc_metadata(cpu_count);
    unsafe {
        allocator
            .init(
                meta_ptr as usize,
                meta_layout.size(),
                heap_addr,
                heap_size,
                cpu_count,
                os,
            )
            .unwrap();
    }
    (meta_ptr, meta_layout)
}

fn slab_alloc_with_refill(
    slab_allocator: &mut SlabByteAllocator<PAGE_SIZE>,
    page_allocator: &mut CompositePageAllocator<PAGE_SIZE>,
    owner_cpu: usize,
    layout: Layout,
) -> core::ptr::NonNull<u8> {
    loop {
        match slab_allocator.alloc(layout).unwrap() {
            SlabAllocDecision::Allocated(ptr, _) => return ptr,
            SlabAllocDecision::NeedsRefill {
                size_class,
                page_count,
                slab_bytes,
            } => {
                let slab_base = page_allocator.alloc_pages(page_count, slab_bytes).unwrap();
                slab_allocator
                    .provide_slab(size_class, owner_cpu, slab_base, slab_bytes)
                    .unwrap();
            }
        }
    }
}

fn slab_dealloc_with_release(
    slab_allocator: &mut SlabByteAllocator<PAGE_SIZE>,
    page_allocator: &mut CompositePageAllocator<PAGE_SIZE>,
    ptr: core::ptr::NonNull<u8>,
    layout: Layout,
) {
    if let SlabDeallocDecision::ReleaseSlab {
        slab_base,
        page_count,
        ..
    } = slab_allocator.dealloc(ptr, layout)
    {
        page_allocator.dealloc_pages(slab_base, page_count);
    }
}

#[test]
fn test_composite_page_allocator_basic() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut allocator = CompositePageAllocator::<PAGE_SIZE>::new();
    allocator.init(heap_addr, TEST_HEAP_SIZE);

    let addr1 = allocator.alloc_pages(1, PAGE_SIZE).unwrap();
    let addr2 = allocator.alloc_pages(4, PAGE_SIZE).unwrap();

    assert!(addr1 >= heap_addr && addr1 < heap_addr + TEST_HEAP_SIZE);
    assert!(addr2 >= heap_addr && addr2 < heap_addr + TEST_HEAP_SIZE);

    allocator.dealloc_pages(addr1, 1);
    allocator.dealloc_pages(addr2, 4);

    dealloc_region(heap_ptr, heap_layout);
}

#[test]
fn test_composite_page_allocator_alignment() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut allocator = CompositePageAllocator::<PAGE_SIZE>::new();
    allocator.init(heap_addr, TEST_HEAP_SIZE);

    let addr1 = allocator.alloc_pages(1, PAGE_SIZE).unwrap();
    let addr2 = allocator.alloc_pages(1, PAGE_SIZE * 2).unwrap();
    let addr3 = allocator.alloc_pages(1, PAGE_SIZE * 4).unwrap();

    assert_eq!(addr1 & (PAGE_SIZE - 1), 0);
    assert_eq!(addr2 & (PAGE_SIZE * 2 - 1), 0);
    assert_eq!(addr3 & (PAGE_SIZE * 4 - 1), 0);

    allocator.dealloc_pages(addr1, 1);
    allocator.dealloc_pages(addr2, 1);
    allocator.dealloc_pages(addr3, 1);

    dealloc_region(heap_ptr, heap_layout);
}

#[test]
fn test_composite_page_allocator_fragmentation() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut allocator = CompositePageAllocator::<PAGE_SIZE>::new();
    allocator.init(heap_addr, TEST_HEAP_SIZE);

    let mut addrs = Vec::new();
    for _ in 0..10 {
        let addr = allocator.alloc_pages(1, PAGE_SIZE).unwrap();
        addrs.push((addr, 1));
    }

    for i in (0..addrs.len()).step_by(2) {
        allocator.dealloc_pages(addrs[i].0, addrs[i].1);
    }

    let result = allocator.alloc_pages(5, PAGE_SIZE);
    assert!(result.is_ok());

    for i in (1..addrs.len()).step_by(2) {
        allocator.dealloc_pages(addrs[i].0, addrs[i].1);
    }
    if let Ok(addr) = result {
        allocator.dealloc_pages(addr, 5);
    }

    dealloc_region(heap_ptr, heap_layout);
}

#[test]
fn test_slab_allocator_basic() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut page_allocator = CompositePageAllocator::<PAGE_SIZE>::new();
    page_allocator.init(heap_addr, TEST_HEAP_SIZE);

    let mut slab_allocator = SlabByteAllocator::<PAGE_SIZE>::new();

    let layout8 = Layout::from_size_align(8, 8).unwrap();
    let ptr8 = slab_alloc_with_refill(&mut slab_allocator, &mut page_allocator, 0, layout8);

    let layout64 = Layout::from_size_align(64, 8).unwrap();
    let ptr64 = slab_alloc_with_refill(&mut slab_allocator, &mut page_allocator, 0, layout64);

    let layout2048 = Layout::from_size_align(2048, 8).unwrap();
    let ptr2048 = slab_alloc_with_refill(&mut slab_allocator, &mut page_allocator, 0, layout2048);

    slab_dealloc_with_release(&mut slab_allocator, &mut page_allocator, ptr8, layout8);
    slab_dealloc_with_release(&mut slab_allocator, &mut page_allocator, ptr64, layout64);
    slab_dealloc_with_release(
        &mut slab_allocator,
        &mut page_allocator,
        ptr2048,
        layout2048,
    );

    dealloc_region(heap_ptr, heap_layout);
}

#[test]
fn test_slab_allocator_many_objects() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut page_allocator = CompositePageAllocator::<PAGE_SIZE>::new();
    page_allocator.init(heap_addr, TEST_HEAP_SIZE);
    let mut slab_allocator = SlabByteAllocator::<PAGE_SIZE>::new();

    let mut ptrs = Vec::new();
    let layout = Layout::from_size_align(32, 8).unwrap();

    for _ in 0..100 {
        let ptr = slab_alloc_with_refill(&mut slab_allocator, &mut page_allocator, 0, layout);
        ptrs.push(ptr);
    }

    assert_eq!(ptrs.len(), 100);

    for ptr in ptrs {
        slab_dealloc_with_release(&mut slab_allocator, &mut page_allocator, ptr, layout);
    }

    dealloc_region(heap_ptr, heap_layout);
}

#[test]
fn test_global_allocator_init() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let (meta_ptr, meta_layout) =
        init_global_allocator(&mut allocator, heap_addr, TEST_HEAP_SIZE, 1);

    let addr = allocator.alloc_pages(1, PAGE_SIZE).unwrap();
    allocator.dealloc_pages(addr, 1);

    dealloc_region(meta_ptr, meta_layout);
    dealloc_region(heap_ptr, heap_layout);
}

#[test]
fn test_global_allocator_small_alloc() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let (meta_ptr, meta_layout) =
        init_global_allocator(&mut allocator, heap_addr, TEST_HEAP_SIZE, 1);

    let layout = Layout::from_size_align(64, 8).unwrap();
    let ptr = allocator.alloc(layout).unwrap();
    allocator.dealloc(ptr, layout);

    dealloc_region(meta_ptr, meta_layout);
    dealloc_region(heap_ptr, heap_layout);
}

#[test]
fn test_global_allocator_large_alloc() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let (meta_ptr, meta_layout) =
        init_global_allocator(&mut allocator, heap_addr, TEST_HEAP_SIZE, 1);

    let layout = Layout::from_size_align(8192, PAGE_SIZE).unwrap();
    let ptr = allocator.alloc(layout).unwrap();
    allocator.dealloc(ptr, layout);

    dealloc_region(meta_ptr, meta_layout);
    dealloc_region(heap_ptr, heap_layout);
}

#[test]
fn test_global_allocator_mixed_alloc() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let (meta_ptr, meta_layout) =
        init_global_allocator(&mut allocator, heap_addr, TEST_HEAP_SIZE, 1);

    let sizes = [8, 64, 1024, 4096, 8192];
    let mut allocations = Vec::new();

    for &size in &sizes {
        let align = if size <= 2048 { 8 } else { PAGE_SIZE };
        let layout = Layout::from_size_align(size, align).unwrap();
        let ptr = allocator.alloc(layout).unwrap();
        allocations.push((ptr, layout));
    }

    for (ptr, layout) in allocations {
        allocator.dealloc(ptr, layout);
    }

    dealloc_region(meta_ptr, meta_layout);
    dealloc_region(heap_ptr, heap_layout);
}

#[test]
fn test_global_allocator_page_alloc() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let (meta_ptr, meta_layout) =
        init_global_allocator(&mut allocator, heap_addr, TEST_HEAP_SIZE, 1);

    let addr1 = allocator.alloc_pages(4, PAGE_SIZE).unwrap();
    let addr2 = allocator.alloc_pages(8, PAGE_SIZE).unwrap();

    allocator.dealloc_pages(addr1, 4);
    allocator.dealloc_pages(addr2, 8);

    dealloc_region(meta_ptr, meta_layout);
    dealloc_region(heap_ptr, heap_layout);
}

#[test]
fn test_global_allocator_add_memory() {
    let (heap_ptr1, heap_layout1) = alloc_test_heap(TEST_HEAP_SIZE);
    let (heap_ptr2, heap_layout2) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr1 = heap_ptr1 as usize;
    let heap_addr2 = heap_ptr2 as usize;

    let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let (meta_ptr, meta_layout) =
        init_global_allocator(&mut allocator, heap_addr1, TEST_HEAP_SIZE, 1);

    allocator.add_memory(heap_addr2, TEST_HEAP_SIZE).unwrap();
    let addr = allocator.alloc_pages(16, PAGE_SIZE).unwrap();
    allocator.dealloc_pages(addr, 16);

    dealloc_region(meta_ptr, meta_layout);
    dealloc_region(heap_ptr1, heap_layout1);
    dealloc_region(heap_ptr2, heap_layout2);
}

#[test]
fn test_error_conditions() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let (meta_ptr, meta_layout) =
        init_global_allocator(&mut allocator, heap_addr, TEST_HEAP_SIZE, 1);

    assert!(matches!(
        allocator.alloc_pages(0, PAGE_SIZE),
        Err(AllocError::InvalidParam)
    ));

    let huge_pages = TEST_HEAP_SIZE / PAGE_SIZE + 1;
    assert!(matches!(
        allocator.alloc_pages(huge_pages, PAGE_SIZE),
        Err(AllocError::NoMemory)
    ));

    dealloc_region(meta_ptr, meta_layout);
    dealloc_region(heap_ptr, heap_layout);
}

#[cfg(feature = "tracking")]
#[test]
fn test_statistics_tracking() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let (meta_ptr, meta_layout) =
        init_global_allocator(&mut allocator, heap_addr, TEST_HEAP_SIZE, 1);

    let stats_initial = allocator.get_stats();
    assert!(stats_initial.total_pages > 0);

    let layout = Layout::from_size_align(64, 8).unwrap();
    let _ptr = allocator.alloc(layout).unwrap();

    let stats_after = allocator.get_stats();
    assert!(stats_after.slab_bytes > 0);

    dealloc_region(meta_ptr, meta_layout);
    dealloc_region(heap_ptr, heap_layout);
}

#[cfg(feature = "tracking")]
#[test]
fn test_buddy_statistics() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let (meta_ptr, meta_layout) =
        init_global_allocator(&mut allocator, heap_addr, TEST_HEAP_SIZE, 1);

    let buddy_stats = allocator.get_buddy_stats();
    assert!(buddy_stats.total_pages > 0);
    assert_eq!(buddy_stats.used_pages, 0);
    assert_eq!(buddy_stats.free_pages, buddy_stats.total_pages);

    dealloc_region(meta_ptr, meta_layout);
    dealloc_region(heap_ptr, heap_layout);
}

#[test]
fn test_stress_allocation_deallocation() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let (meta_ptr, meta_layout) = init_global_allocator_with_os(
        &mut allocator,
        heap_addr,
        TEST_HEAP_SIZE,
        2,
        &SWITCHING_OS,
    );

    let mut allocations = Vec::new();
    for i in 0..100 {
        SWITCHING_OS.set_cpu(i % 2);
        let size = if i % 2 == 0 { 64 } else { 4096 };
        let align = if size <= 2048 { 8 } else { PAGE_SIZE };
        let layout = Layout::from_size_align(size, align).unwrap();
        if let Ok(ptr) = allocator.alloc(layout) {
            allocations.push((ptr, layout));
        }
    }

    while let Some((ptr, layout)) = allocations.pop() {
        allocator.dealloc(ptr, layout);
    }

    dealloc_region(meta_ptr, meta_layout);
    dealloc_region(heap_ptr, heap_layout);
}

#[test]
fn test_global_allocator_cross_cpu_free() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let (meta_ptr, meta_layout) = init_global_allocator_with_os(
        &mut allocator,
        heap_addr,
        TEST_HEAP_SIZE,
        2,
        &SWITCHING_OS,
    );

    let layout = Layout::from_size_align(64, 8).unwrap();
    SWITCHING_OS.set_cpu(0);
    let ptr = allocator.alloc(layout).unwrap();

    SWITCHING_OS.set_cpu(1);
    allocator.dealloc(ptr, layout);

    SWITCHING_OS.set_cpu(0);
    let ptr2 = allocator.alloc(layout).unwrap();
    allocator.dealloc(ptr2, layout);

    dealloc_region(meta_ptr, meta_layout);
    dealloc_region(heap_ptr, heap_layout);
}
