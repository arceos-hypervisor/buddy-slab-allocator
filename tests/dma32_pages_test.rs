//! Tests for lowmem (DMA32) page allocation via GlobalAllocator.

extern crate buddy_slab_allocator;

use buddy_slab_allocator::{GlobalAllocator, OsImpl};
use core::alloc::Layout;
use std::alloc::{alloc, dealloc};

const PAGE_SIZE: usize = 0x1000;
const TEST_HEAP_SIZE: usize = 16 * 1024 * 1024;

struct MockOs;

impl OsImpl for MockOs {
    fn current_cpu_idx(&self) -> usize {
        0
    }
    fn virt_to_phys(&self, vaddr: usize) -> usize {
        // Map virtual addresses below 4 GiB so lowmem checks pass.
        vaddr & 0x0FFF_FFFF
    }
    fn phys_to_virt(&self, paddr: usize) -> usize {
        paddr
    }
}

static MOCK_OS: MockOs = MockOs;

fn host_alloc(size: usize, align: usize) -> (*mut u8, Layout) {
    let layout = Layout::from_size_align(size, align).unwrap();
    let ptr = unsafe { alloc(layout) };
    assert!(!ptr.is_null());
    (ptr, layout)
}

fn host_dealloc(ptr: *mut u8, layout: Layout) {
    unsafe { dealloc(ptr, layout) };
}

fn init_allocator(
    allocator: &GlobalAllocator<PAGE_SIZE>,
    heap_addr: usize,
    heap_size: usize,
) -> (*mut u8, Layout) {
    let meta_size = GlobalAllocator::<PAGE_SIZE>::required_metadata_size(heap_size, 1);
    let meta_align = GlobalAllocator::<PAGE_SIZE>::required_metadata_align().max(8);
    let (meta_ptr, meta_layout) = host_alloc(meta_size, meta_align);
    unsafe {
        allocator
            .init(meta_ptr, meta_size, heap_addr, heap_size, 1, &MOCK_OS)
            .unwrap();
    }
    (meta_ptr, meta_layout)
}

#[test]
fn test_lowmem_basic() {
    let (heap_ptr, heap_layout) = host_alloc(TEST_HEAP_SIZE, PAGE_SIZE);
    let heap_addr = heap_ptr as usize;
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let (meta_ptr, meta_layout) = init_allocator(&allocator, heap_addr, TEST_HEAP_SIZE);

    let addr1 = allocator.alloc_pages_lowmem(1, PAGE_SIZE).unwrap();
    let addr2 = allocator.alloc_pages_lowmem(4, PAGE_SIZE).unwrap();

    assert!(addr1 >= heap_addr && addr1 < heap_addr + TEST_HEAP_SIZE);
    assert!(addr2 >= heap_addr && addr2 < heap_addr + TEST_HEAP_SIZE);
    assert_eq!(addr1 % PAGE_SIZE, 0);
    assert_eq!(addr2 % PAGE_SIZE, 0);

    allocator.dealloc_pages(addr1, 1);
    allocator.dealloc_pages(addr2, 4);

    host_dealloc(meta_ptr, meta_layout);
    host_dealloc(heap_ptr, heap_layout);
}

#[test]
fn test_lowmem_aligned() {
    let (heap_ptr, heap_layout) = host_alloc(TEST_HEAP_SIZE, PAGE_SIZE * 2);
    let heap_addr = heap_ptr as usize;
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let (meta_ptr, meta_layout) = init_allocator(&allocator, heap_addr, TEST_HEAP_SIZE);

    let addr = allocator.alloc_pages_lowmem(1, 2 * PAGE_SIZE).unwrap();
    assert_eq!(addr % (2 * PAGE_SIZE), 0);
    allocator.dealloc_pages(addr, 1);

    host_dealloc(meta_ptr, meta_layout);
    host_dealloc(heap_ptr, heap_layout);
}

#[test]
fn test_lowmem_vs_normal() {
    let (heap_ptr, heap_layout) = host_alloc(TEST_HEAP_SIZE, PAGE_SIZE);
    let heap_addr = heap_ptr as usize;
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let (meta_ptr, meta_layout) = init_allocator(&allocator, heap_addr, TEST_HEAP_SIZE);

    let addr_low = allocator.alloc_pages_lowmem(1, PAGE_SIZE).unwrap();
    let addr_normal = allocator.alloc_pages(1, PAGE_SIZE).unwrap();

    assert!(addr_low >= heap_addr);
    assert!(addr_normal >= heap_addr);

    allocator.dealloc_pages(addr_low, 1);
    allocator.dealloc_pages(addr_normal, 1);

    host_dealloc(meta_ptr, meta_layout);
    host_dealloc(heap_ptr, heap_layout);
}

#[test]
fn test_lowmem_stress() {
    let (heap_ptr, heap_layout) = host_alloc(TEST_HEAP_SIZE, PAGE_SIZE);
    let heap_addr = heap_ptr as usize;
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let (meta_ptr, meta_layout) = init_allocator(&allocator, heap_addr, TEST_HEAP_SIZE);

    let mut addrs = Vec::new();
    for _ in 0..32 {
        let addr = allocator.alloc_pages_lowmem(1, PAGE_SIZE).unwrap();
        addrs.push(addr);
    }
    for addr in addrs {
        allocator.dealloc_pages(addr, 1);
    }

    host_dealloc(meta_ptr, meta_layout);
    host_dealloc(heap_ptr, heap_layout);
}
