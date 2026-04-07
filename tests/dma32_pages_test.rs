//! Tests for GlobalAllocator's alloc_dma32_pages method.

#![no_std]

extern crate alloc;

use buddy_slab_allocator::{AddrTranslator, AllocError, GlobalAllocator, Os};
use core::alloc::Layout;
use core::sync::atomic::{AtomicUsize, Ordering};

const PAGE_SIZE: usize = 0x1000;
const TEST_HEAP_SIZE: usize = 16 * 1024 * 1024;

struct MockAddrTranslator;

impl AddrTranslator for MockAddrTranslator {
    fn virt_to_phys(&self, va: usize) -> Option<usize> {
        Some(va & 0x7fff_ffff)
    }
}

struct MockOs {
    cpu: AtomicUsize,
}

impl MockOs {
    const fn new() -> Self {
        Self {
            cpu: AtomicUsize::new(0),
        }
    }
}

impl Os for MockOs {
    fn current_cpu_idx(&self) -> usize {
        self.cpu.load(Ordering::Relaxed)
    }
}

static MOCK_TRANSLATOR: MockAddrTranslator = MockAddrTranslator;
static MOCK_OS: MockOs = MockOs::new();

fn alloc_region(size: usize, align: usize) -> (*mut u8, Layout) {
    let layout = Layout::from_size_align(size, align).unwrap();
    let ptr = unsafe { alloc::alloc::alloc(layout) };
    assert!(!ptr.is_null(), "Failed to allocate region");
    (ptr, layout)
}

fn dealloc_region(ptr: *mut u8, layout: Layout) {
    unsafe { alloc::alloc::dealloc(ptr, layout) };
}

fn alloc_metadata(cpu_count: usize) -> (*mut u8, Layout) {
    alloc_region(
        GlobalAllocator::<PAGE_SIZE>::required_metadata_size(cpu_count),
        PAGE_SIZE,
    )
}

fn init_allocator(
    allocator: &mut GlobalAllocator<PAGE_SIZE>,
    heap_addr: usize,
    heap_size: usize,
) -> (*mut u8, Layout) {
    let (meta_ptr, meta_layout) = alloc_metadata(1);
    allocator.set_addr_translator(&MOCK_TRANSLATOR);
    unsafe {
        allocator
            .init(
                meta_ptr as usize,
                meta_layout.size(),
                heap_addr,
                heap_size,
                1,
                &MOCK_OS,
            )
            .unwrap();
    }
    (meta_ptr, meta_layout)
}

#[test]
fn test_alloc_dma32_pages_uninitialized() {
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let result = allocator.alloc_dma32_pages(1, PAGE_SIZE);
    assert!(matches!(result, Err(AllocError::NoMemory)));
}

#[test]
fn test_alloc_dma32_pages_initialized() {
    let (heap_ptr, heap_layout) = alloc_region(TEST_HEAP_SIZE, PAGE_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let (meta_ptr, meta_layout) = init_allocator(&mut allocator, heap_addr, TEST_HEAP_SIZE);

    let addr1 = allocator.alloc_dma32_pages(1, PAGE_SIZE).unwrap();
    let addr2 = allocator.alloc_dma32_pages(4, PAGE_SIZE).unwrap();
    let addr3 = allocator.alloc_dma32_pages(1, 2 * PAGE_SIZE).unwrap();

    assert!(addr1 >= heap_addr && addr1 < heap_addr + TEST_HEAP_SIZE);
    assert!(addr2 >= heap_addr && addr2 < heap_addr + TEST_HEAP_SIZE);
    assert!(addr3 >= heap_addr && addr3 < heap_addr + TEST_HEAP_SIZE);
    assert_eq!(addr1 % PAGE_SIZE, 0);
    assert_eq!(addr2 % PAGE_SIZE, 0);
    assert_eq!(addr3 % (2 * PAGE_SIZE), 0);

    allocator.dealloc_pages(addr1, 1);
    allocator.dealloc_pages(addr2, 4);
    allocator.dealloc_pages(addr3, 1);

    dealloc_region(meta_ptr, meta_layout);
    dealloc_region(heap_ptr, heap_layout);
}

#[test]
fn test_alloc_dma32_pages_memory_stats() {
    let (heap_ptr, heap_layout) = alloc_region(TEST_HEAP_SIZE, PAGE_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let (meta_ptr, meta_layout) = init_allocator(&mut allocator, heap_addr, TEST_HEAP_SIZE);

    #[cfg(feature = "tracking")]
    {
        let stats_before = allocator.get_stats();
        assert!(stats_before.total_pages > 0);
    }

    let addr = allocator.alloc_dma32_pages(2, PAGE_SIZE).unwrap();
    allocator.dealloc_pages(addr, 2);

    #[cfg(feature = "tracking")]
    {
        let stats_after = allocator.get_stats();
        assert!(stats_after.total_pages > 0);
    }

    dealloc_region(meta_ptr, meta_layout);
    dealloc_region(heap_ptr, heap_layout);
}

#[test]
fn test_alloc_dma32_pages_vs_normal_pages() {
    let (heap_ptr, heap_layout) = alloc_region(TEST_HEAP_SIZE, PAGE_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let (meta_ptr, meta_layout) = init_allocator(&mut allocator, heap_addr, TEST_HEAP_SIZE);

    let addr_dma32 = allocator.alloc_dma32_pages(1, PAGE_SIZE).unwrap();
    let addr_normal = allocator.alloc_pages(1, PAGE_SIZE).unwrap();

    assert!(addr_dma32 >= heap_addr && addr_dma32 < heap_addr + TEST_HEAP_SIZE);
    assert!(addr_normal >= heap_addr && addr_normal < heap_addr + TEST_HEAP_SIZE);

    allocator.dealloc_pages(addr_dma32, 1);
    allocator.dealloc_pages(addr_normal, 1);

    dealloc_region(meta_ptr, meta_layout);
    dealloc_region(heap_ptr, heap_layout);
}

#[test]
fn test_alloc_dma32_pages_stress() {
    let (heap_ptr, heap_layout) = alloc_region(TEST_HEAP_SIZE, PAGE_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let (meta_ptr, meta_layout) = init_allocator(&mut allocator, heap_addr, TEST_HEAP_SIZE);

    let mut addrs = alloc::vec::Vec::new();
    for _ in 0..32 {
        let addr = allocator.alloc_dma32_pages(1, PAGE_SIZE).unwrap();
        addrs.push(addr);
    }

    for addr in addrs {
        allocator.dealloc_pages(addr, 1);
    }

    dealloc_region(meta_ptr, meta_layout);
    dealloc_region(heap_ptr, heap_layout);
}
