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
    region_addr: usize,
    region_size: usize,
) {
    unsafe { allocator.init(region_addr, region_size, 1, &MOCK_OS).unwrap() };
}

#[test]
fn test_lowmem_basic() {
    let (region_ptr, region_layout) = host_alloc(TEST_HEAP_SIZE, PAGE_SIZE);
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    init_allocator(&allocator, region_ptr as usize, TEST_HEAP_SIZE);
    let managed_start = allocator.managed_heap_start();
    let managed_end = managed_start + allocator.managed_heap_size();

    let addr1 = allocator.alloc_pages_lowmem(1, PAGE_SIZE).unwrap();
    let addr2 = allocator.alloc_pages_lowmem(4, PAGE_SIZE).unwrap();

    assert!(addr1 >= managed_start && addr1 < managed_end);
    assert!(addr2 >= managed_start && addr2 < managed_end);
    assert_eq!(addr1 % PAGE_SIZE, 0);
    assert_eq!(addr2 % PAGE_SIZE, 0);

    allocator.dealloc_pages(addr1, 1);
    allocator.dealloc_pages(addr2, 4);

    host_dealloc(region_ptr, region_layout);
}

#[test]
fn test_lowmem_aligned() {
    let (region_ptr, region_layout) = host_alloc(TEST_HEAP_SIZE, PAGE_SIZE * 2);
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    init_allocator(&allocator, region_ptr as usize, TEST_HEAP_SIZE);

    let addr = allocator.alloc_pages_lowmem(1, 2 * PAGE_SIZE).unwrap();
    assert_eq!(
        (addr - allocator.managed_heap_start()) % (2 * PAGE_SIZE),
        0
    );
    allocator.dealloc_pages(addr, 1);

    host_dealloc(region_ptr, region_layout);
}

#[test]
fn test_lowmem_vs_normal() {
    let (region_ptr, region_layout) = host_alloc(TEST_HEAP_SIZE, PAGE_SIZE);
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    init_allocator(&allocator, region_ptr as usize, TEST_HEAP_SIZE);

    let addr_low = allocator.alloc_pages_lowmem(1, PAGE_SIZE).unwrap();
    let addr_normal = allocator.alloc_pages(1, PAGE_SIZE).unwrap();

    assert!(addr_low >= allocator.managed_heap_start());
    assert!(addr_normal >= allocator.managed_heap_start());

    allocator.dealloc_pages(addr_low, 1);
    allocator.dealloc_pages(addr_normal, 1);

    host_dealloc(region_ptr, region_layout);
}

#[test]
fn test_lowmem_stress() {
    let (region_ptr, region_layout) = host_alloc(TEST_HEAP_SIZE, PAGE_SIZE);
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    init_allocator(&allocator, region_ptr as usize, TEST_HEAP_SIZE);

    let mut addrs = Vec::new();
    for _ in 0..32 {
        let addr = allocator.alloc_pages_lowmem(1, PAGE_SIZE).unwrap();
        addrs.push(addr);
    }
    for addr in addrs {
        allocator.dealloc_pages(addr, 1);
    }

    host_dealloc(region_ptr, region_layout);
}
