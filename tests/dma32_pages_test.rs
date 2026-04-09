//! Tests for lowmem (DMA32) page allocation via GlobalAllocator.

extern crate buddy_slab_allocator;

mod common;

use buddy_slab_allocator::GlobalAllocator;
use common::{init_global, HostRegion, LOWMEM_OS};

const PAGE_SIZE: usize = 0x1000;
const TEST_HEAP_SIZE: usize = 16 * 1024 * 1024;

fn init_allocator(allocator: &GlobalAllocator<PAGE_SIZE>, region: &mut HostRegion) {
    init_global(allocator, region, 1, &LOWMEM_OS);
}

#[test]
fn test_lowmem_basic() {
    let mut region = HostRegion::new(TEST_HEAP_SIZE, PAGE_SIZE);
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    init_allocator(&allocator, &mut region);
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
}

#[test]
fn test_lowmem_aligned() {
    let mut region = HostRegion::new(TEST_HEAP_SIZE, PAGE_SIZE * 2);
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    init_allocator(&allocator, &mut region);

    let addr = allocator.alloc_pages_lowmem(1, 2 * PAGE_SIZE).unwrap();
    assert_eq!((addr - allocator.managed_heap_start()) % (2 * PAGE_SIZE), 0);
    allocator.dealloc_pages(addr, 1);
}

#[test]
fn test_lowmem_vs_normal() {
    let mut region = HostRegion::new(TEST_HEAP_SIZE, PAGE_SIZE);
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    init_allocator(&allocator, &mut region);

    let addr_low = allocator.alloc_pages_lowmem(1, PAGE_SIZE).unwrap();
    let addr_normal = allocator.alloc_pages(1, PAGE_SIZE).unwrap();

    assert!(addr_low >= allocator.managed_heap_start());
    assert!(addr_normal >= allocator.managed_heap_start());

    allocator.dealloc_pages(addr_low, 1);
    allocator.dealloc_pages(addr_normal, 1);
}

#[test]
fn test_lowmem_stress() {
    let mut region = HostRegion::new(TEST_HEAP_SIZE, PAGE_SIZE);
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    init_allocator(&allocator, &mut region);

    let mut addrs = Vec::new();
    for _ in 0..32 {
        let addr = allocator.alloc_pages_lowmem(1, PAGE_SIZE).unwrap();
        addrs.push(addr);
    }
    for addr in addrs {
        allocator.dealloc_pages(addr, 1);
    }
}
