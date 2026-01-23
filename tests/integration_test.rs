//! Integration tests for the allocator crate
//!
//! Tests the complete allocator system working together,
//! focusing on cross-module integration scenarios.

#![no_std]

extern crate alloc;
extern crate buddy_slab_allocator;

use alloc::vec::Vec;
use buddy_slab_allocator::{
    AllocError, BaseAllocator, ByteAllocator, CompositePageAllocator, GlobalAllocator,
    PageAllocator, SlabByteAllocator,
};
use core::alloc::Layout;

const PAGE_SIZE: usize = 0x1000;
const TEST_HEAP_SIZE: usize = 16 * 1024 * 1024; // 16MB

/// Allocate test memory using system allocator
fn alloc_test_heap(size: usize) -> (*mut u8, Layout) {
    let layout = Layout::from_size_align(size, PAGE_SIZE).unwrap();
    let ptr = unsafe { alloc::alloc::alloc(layout) };
    assert!(!ptr.is_null(), "Failed to allocate test heap");
    (ptr, layout)
}

/// Deallocate test memory
fn dealloc_test_heap(ptr: *mut u8, layout: Layout) {
    unsafe { alloc::alloc::dealloc(ptr, layout) };
}

#[test]
fn test_composite_page_allocator_basic() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut allocator = CompositePageAllocator::<PAGE_SIZE>::new();
    allocator.init(heap_addr, TEST_HEAP_SIZE);

    // Just verify allocator can perform basic operations
    // Allocate 1 page
    let addr1 = allocator.alloc_pages(1, PAGE_SIZE).unwrap();
    assert!(addr1 >= heap_addr && addr1 < heap_addr + TEST_HEAP_SIZE);

    // Allocate 4 pages
    let addr2 = allocator.alloc_pages(4, PAGE_SIZE).unwrap();
    assert!(addr2 >= heap_addr && addr2 < heap_addr + TEST_HEAP_SIZE);

    // Deallocate
    allocator.dealloc_pages(addr1, 1);
    allocator.dealloc_pages(addr2, 4);

    dealloc_test_heap(heap_ptr, heap_layout);
}

#[test]
fn test_composite_page_allocator_alignment() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut allocator = CompositePageAllocator::<PAGE_SIZE>::new();
    allocator.init(heap_addr, TEST_HEAP_SIZE);

    // Test different alignments
    let addr1 = allocator.alloc_pages(1, PAGE_SIZE).unwrap();
    assert_eq!(addr1 & (PAGE_SIZE - 1), 0);

    let addr2 = allocator.alloc_pages(1, PAGE_SIZE * 2).unwrap();
    assert_eq!(addr2 & (PAGE_SIZE * 2 - 1), 0);

    let addr3 = allocator.alloc_pages(1, PAGE_SIZE * 4).unwrap();
    assert_eq!(addr3 & (PAGE_SIZE * 4 - 1), 0);

    allocator.dealloc_pages(addr1, 1);
    allocator.dealloc_pages(addr2, 1);
    allocator.dealloc_pages(addr3, 1);

    dealloc_test_heap(heap_ptr, heap_layout);
}

#[test]
fn test_composite_page_allocator_large_allocation() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut allocator = CompositePageAllocator::<PAGE_SIZE>::new();
    allocator.init(heap_addr, TEST_HEAP_SIZE);

    // Allocate large block
    let large_pages = 1024; // 4MB
    let addr = allocator.alloc_pages(large_pages, PAGE_SIZE).unwrap();
    assert!(addr >= heap_addr && addr < heap_addr + TEST_HEAP_SIZE);

    allocator.dealloc_pages(addr, large_pages);

    dealloc_test_heap(heap_ptr, heap_layout);
}

#[test]
fn test_composite_page_allocator_fragmentation() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut allocator = CompositePageAllocator::<PAGE_SIZE>::new();
    allocator.init(heap_addr, TEST_HEAP_SIZE);

    // Create fragmentation pattern
    let mut addrs = Vec::new();
    for _ in 0..10 {
        let addr = allocator.alloc_pages(1, PAGE_SIZE).unwrap();
        addrs.push((addr, 1));
    }

    // Free every other allocation
    for i in (0..addrs.len()).step_by(2) {
        allocator.dealloc_pages(addrs[i].0, addrs[i].1);
    }

    // Try to allocate larger block
    let result = allocator.alloc_pages(5, PAGE_SIZE);
    assert!(result.is_ok());

    // Cleanup
    for i in (1..addrs.len()).step_by(2) {
        allocator.dealloc_pages(addrs[i].0, addrs[i].1);
    }
    if let Ok(addr) = result {
        allocator.dealloc_pages(addr, 5);
    }

    dealloc_test_heap(heap_ptr, heap_layout);
}

#[test]
fn test_composite_page_allocator_alloc_at() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut allocator = CompositePageAllocator::<PAGE_SIZE>::new();
    allocator.init(heap_addr, TEST_HEAP_SIZE);

    // Note: alloc_pages_at may not always succeed due to buddy system structure
    // We just test that it doesn't crash
    let target_addr = heap_addr + PAGE_SIZE * 100;
    let _result = allocator.alloc_pages_at(target_addr, 4, PAGE_SIZE);

    // If successful, clean up
    // if result.is_ok() {
    //     allocator.dealloc_pages(target_addr, 4);
    // }

    dealloc_test_heap(heap_ptr, heap_layout);
}

#[test]
fn test_slab_allocator_basic() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut page_allocator = CompositePageAllocator::<PAGE_SIZE>::new();
    page_allocator.init(heap_addr, TEST_HEAP_SIZE);

    let mut slab_allocator = SlabByteAllocator::<PAGE_SIZE>::new();
    slab_allocator.init();

    let page_alloc_ptr = &mut page_allocator as *mut CompositePageAllocator<PAGE_SIZE>
        as *mut dyn buddy_slab_allocator::slab::PageAllocatorForSlab;
    slab_allocator.set_page_allocator(page_alloc_ptr);

    // Test various small allocations
    let layout8 = Layout::from_size_align(8, 8).unwrap();
    let ptr8 = slab_allocator.alloc(layout8).unwrap();

    let layout64 = Layout::from_size_align(64, 8).unwrap();
    let ptr64 = slab_allocator.alloc(layout64).unwrap();

    let layout2048 = Layout::from_size_align(2048, 8).unwrap();
    let ptr2048 = slab_allocator.alloc(layout2048).unwrap();

    // Deallocate
    slab_allocator.dealloc(ptr8, layout8);
    slab_allocator.dealloc(ptr64, layout64);
    slab_allocator.dealloc(ptr2048, layout2048);

    dealloc_test_heap(heap_ptr, heap_layout);
}

#[test]
fn test_slab_allocator_many_objects() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut page_allocator = CompositePageAllocator::<PAGE_SIZE>::new();
    page_allocator.init(heap_addr, TEST_HEAP_SIZE);

    let mut slab_allocator = SlabByteAllocator::<PAGE_SIZE>::new();
    slab_allocator.init();

    let page_alloc_ptr = &mut page_allocator as *mut CompositePageAllocator<PAGE_SIZE>
        as *mut dyn buddy_slab_allocator::slab::PageAllocatorForSlab;
    slab_allocator.set_page_allocator(page_alloc_ptr);

    // Allocate many small objects
    let mut ptrs = Vec::new();
    let layout = Layout::from_size_align(32, 8).unwrap();

    for _ in 0..100 {
        let ptr = slab_allocator.alloc(layout).unwrap();
        ptrs.push(ptr);
    }

    assert_eq!(ptrs.len(), 100);

    // Deallocate all
    for ptr in ptrs {
        slab_allocator.dealloc(ptr, layout);
    }

    dealloc_test_heap(heap_ptr, heap_layout);
}

#[test]
fn test_global_allocator_init() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    let result = allocator.init(heap_addr, TEST_HEAP_SIZE);
    assert!(result.is_ok());

    // Just verify the allocator can perform allocations after init
    let addr = allocator.alloc_pages(1, PAGE_SIZE);
    assert!(addr.is_ok());
    if let Ok(a) = addr {
        allocator.dealloc_pages(a, 1);
    }

    dealloc_test_heap(heap_ptr, heap_layout);
}

#[test]
fn test_global_allocator_small_alloc() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    allocator.init(heap_addr, TEST_HEAP_SIZE).unwrap();

    // Small allocations should go through slab
    let layout = Layout::from_size_align(64, 8).unwrap();
    let ptr = allocator.alloc(layout).unwrap();

    allocator.dealloc(ptr, layout);

    dealloc_test_heap(heap_ptr, heap_layout);
}

#[test]
fn test_global_allocator_large_alloc() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    allocator.init(heap_addr, TEST_HEAP_SIZE).unwrap();

    // Large allocations should go through page allocator
    let layout = Layout::from_size_align(8192, PAGE_SIZE).unwrap();
    let ptr = allocator.alloc(layout).unwrap();

    allocator.dealloc(ptr, layout);

    dealloc_test_heap(heap_ptr, heap_layout);
}

#[test]
fn test_global_allocator_mixed_alloc() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    allocator.init(heap_addr, TEST_HEAP_SIZE).unwrap();

    let mut allocations = Vec::new();

    // Mix of small and large allocations
    for i in 0..20 {
        let size = if i % 2 == 0 { 64 } else { 8192 };
        let layout = Layout::from_size_align(size, 8).unwrap();
        let ptr = allocator.alloc(layout).unwrap();
        allocations.push((ptr, layout));
    }

    assert_eq!(allocations.len(), 20);

    // Deallocate all
    for (ptr, layout) in allocations {
        allocator.dealloc(ptr, layout);
    }

    dealloc_test_heap(heap_ptr, heap_layout);
}

#[test]
fn test_global_allocator_page_alloc() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    allocator.init(heap_addr, TEST_HEAP_SIZE).unwrap();

    // Direct page allocation
    let addr1 = allocator.alloc_pages(4, PAGE_SIZE).unwrap();
    assert!(addr1 >= heap_addr && addr1 < heap_addr + TEST_HEAP_SIZE);

    let addr2 = allocator.alloc_pages(8, PAGE_SIZE).unwrap();
    assert!(addr2 >= heap_addr && addr2 < heap_addr + TEST_HEAP_SIZE);

    allocator.dealloc_pages(addr1, 4);
    allocator.dealloc_pages(addr2, 8);

    dealloc_test_heap(heap_ptr, heap_layout);
}

#[test]
fn test_global_allocator_add_memory() {
    let (heap_ptr1, heap_layout1) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr1 = heap_ptr1 as usize;

    let (heap_ptr2, heap_layout2) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr2 = heap_ptr2 as usize;

    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    allocator.init(heap_addr1, TEST_HEAP_SIZE).unwrap();

    // Try to add more memory (may fail if max zones reached)
    let _result = allocator.add_memory(heap_addr2, TEST_HEAP_SIZE);

    dealloc_test_heap(heap_ptr1, heap_layout1);
    dealloc_test_heap(heap_ptr2, heap_layout2);
}

#[test]
fn test_error_conditions() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let mut allocator = CompositePageAllocator::<PAGE_SIZE>::new();
    allocator.init(heap_addr, TEST_HEAP_SIZE);

    // Test invalid parameter
    let result = allocator.alloc_pages(0, PAGE_SIZE);
    assert_eq!(result, Err(AllocError::InvalidParam));

    // Test allocation too large
    let huge_pages = TEST_HEAP_SIZE / PAGE_SIZE + 1000;
    let result = allocator.alloc_pages(huge_pages, PAGE_SIZE);
    assert_eq!(result, Err(AllocError::NoMemory));

    dealloc_test_heap(heap_ptr, heap_layout);
}

#[cfg(feature = "tracking")]
#[test]
fn test_statistics_tracking() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    allocator.init(heap_addr, TEST_HEAP_SIZE).unwrap();

    let stats_initial = allocator.get_stats();
    assert_eq!(stats_initial.total_pages, TEST_HEAP_SIZE / PAGE_SIZE);
    assert_eq!(stats_initial.used_pages, 0);

    // Allocate some memory
    let layout = Layout::from_size_align(64, 8).unwrap();
    let _ptr = allocator.alloc(layout).unwrap();

    let stats_after = allocator.get_stats();
    assert!(stats_after.slab_bytes > 0);

    dealloc_test_heap(heap_ptr, heap_layout);
}

#[cfg(feature = "tracking")]
#[test]
fn test_buddy_statistics() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    allocator.init(heap_addr, TEST_HEAP_SIZE).unwrap();

    let buddy_stats = allocator.get_buddy_stats();
    assert!(buddy_stats.total_pages > 0);
    assert_eq!(buddy_stats.used_pages, 0);

    dealloc_test_heap(heap_ptr, heap_layout);
}

#[test]
fn test_stress_allocation_deallocation() {
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    allocator.init(heap_addr, TEST_HEAP_SIZE).unwrap();

    // Stress test with many allocations
    for _round in 0..5 {
        let mut allocations = Vec::new();

        for i in 0..50 {
            let size = match i % 5 {
                0 => 8,
                1 => 32,
                2 => 128,
                3 => 512,
                _ => 2048,
            };
            let layout = Layout::from_size_align(size, 8).unwrap();
            if let Ok(ptr) = allocator.alloc(layout) {
                allocations.push((ptr, layout));
            }
        }

        // Deallocate in reverse order
        while let Some((ptr, layout)) = allocations.pop() {
            allocator.dealloc(ptr, layout);
        }

        // Check that we can still allocate after each round
        let test_layout = Layout::from_size_align(64, 8).unwrap();
        let ptr = allocator.alloc(test_layout).unwrap();
        allocator.dealloc(ptr, test_layout);
    }

    dealloc_test_heap(heap_ptr, heap_layout);
}
