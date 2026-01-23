//! Test for GlobalAllocator's alloc_dma32_pages method

#![no_std]

extern crate alloc;

use alloc::vec;
use alloc::vec::Vec;
use buddy_slab_allocator::{AddrTranslator, AllocError, GlobalAllocator};
use core::alloc::Layout;

const PAGE_SIZE: usize = 0x1000; // 4KB pages
const TEST_HEAP_SIZE: usize = 16 * 1024 * 1024; // 16MB

/// Mock address translator for testing
/// In a real hypervisor, this would translate virtual addresses to physical addresses
struct MockAddrTranslator;

impl AddrTranslator for MockAddrTranslator {
    fn virt_to_phys(&self, va: usize) -> Option<usize> {
        // For testing purposes, we'll map virtual addresses to physical addresses in the low-memory region
        // This ensures that our test memory is considered low-memory (<4GiB)
        // We'll simply subtract a large value to get into the low-memory range
        Some(va & 0x7fffffff) // Mask to get 31-bit address, which is below 2GiB
    }
}

/// Static instance of the mock address translator
static MOCK_TRANSLATOR: MockAddrTranslator = MockAddrTranslator;

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
fn test_alloc_dma32_pages_uninitialized() {
    // Create a new allocator but don't initialize it
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();

    // Try to allocate pages - should fail because allocator is not initialized
    let result = allocator.alloc_dma32_pages(1, PAGE_SIZE);
    assert!(
        result.is_err(),
        "Expected error when allocating from uninitialized allocator"
    );
    assert_eq!(
        result.unwrap_err(),
        AllocError::NoMemory,
        "Expected NoMemory error"
    );
}

#[test]
fn test_alloc_dma32_pages_initialized() {
    // Allocate actual test memory
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    // Create allocator and set address translator
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    allocator.set_addr_translator(&MOCK_TRANSLATOR);

    // Initialize allocator
    let init_result = allocator.init(heap_addr, TEST_HEAP_SIZE);
    assert!(
        init_result.is_ok(),
        "Failed to initialize allocator: {:?}",
        init_result
    );

    // Test 1: Allocate 1 page with page size alignment
    let result1 = allocator.alloc_dma32_pages(1, PAGE_SIZE);
    assert!(result1.is_ok(), "Failed to allocate 1 page: {:?}", result1);
    let addr1 = result1.unwrap();
    assert!(
        addr1 >= heap_addr,
        "Allocated address is below memory start"
    );
    assert!(
        addr1 < heap_addr + TEST_HEAP_SIZE,
        "Allocated address is beyond memory end"
    );
    assert_eq!(
        addr1 % PAGE_SIZE,
        0,
        "Allocated address is not page-aligned"
    );

    // Test 2: Allocate multiple pages
    let result2 = allocator.alloc_dma32_pages(4, PAGE_SIZE);
    assert!(result2.is_ok(), "Failed to allocate 4 pages: {:?}", result2);
    let addr2 = result2.unwrap();
    assert!(
        addr2 >= heap_addr,
        "Allocated address is below memory start"
    );
    assert!(
        addr2 < heap_addr + TEST_HEAP_SIZE,
        "Allocated address is beyond memory end"
    );
    assert_eq!(
        addr2 % PAGE_SIZE,
        0,
        "Allocated address is not page-aligned"
    );

    // Test 3: Allocate with different alignment
    let result3 = allocator.alloc_dma32_pages(1, 2 * PAGE_SIZE); // 8KB alignment
    assert!(
        result3.is_ok(),
        "Failed to allocate 1 page with 8KB alignment: {:?}",
        result3
    );
    let addr3 = result3.unwrap();
    assert!(
        addr3 >= heap_addr,
        "Allocated address is below memory start"
    );
    assert!(
        addr3 < heap_addr + TEST_HEAP_SIZE,
        "Allocated address is beyond memory end"
    );
    assert_eq!(
        addr3 % (2 * PAGE_SIZE),
        0,
        "Allocated address is not 8KB-aligned"
    );

    // Clean up
    dealloc_test_heap(heap_ptr, heap_layout);
}

#[test]
fn test_alloc_dma32_pages_memory_structure() {
    // Allocate actual test memory
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    // Create allocator and set address translator
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    allocator.set_addr_translator(&MOCK_TRANSLATOR);

    // Initialize allocator
    let init_result = allocator.init(heap_addr, TEST_HEAP_SIZE);
    assert!(
        init_result.is_ok(),
        "Failed to initialize allocator: {:?}",
        init_result
    );

    // Test basic memory structure by allocating and deallocating
    // This will exercise the internal memory management structures

    // Allocate some DMA32 pages
    let alloc_results = vec![
        allocator.alloc_dma32_pages(1, PAGE_SIZE),
        allocator.alloc_dma32_pages(2, PAGE_SIZE),
        allocator.alloc_dma32_pages(4, PAGE_SIZE),
    ];

    // Verify all allocations succeeded
    for (i, result) in alloc_results.iter().enumerate() {
        assert!(
            result.is_ok(),
            "Failed to allocate DMA32 pages (iteration {}): {:?}",
            i,
            result
        );
    }

    // Get allocated addresses
    let alloc_addrs: Vec<usize> = alloc_results.into_iter().map(|r| r.unwrap()).collect();

    // Verify all addresses are valid
    for addr in &alloc_addrs {
        assert!(
            addr >= &heap_addr,
            "Allocated address is below memory start"
        );
        assert!(
            addr < &(heap_addr + TEST_HEAP_SIZE),
            "Allocated address is beyond memory end"
        );
    }

    // Test memory statistics if tracking feature is enabled
    #[cfg(feature = "tracking")]
    {
        // Get statistics after allocations
        let stats_after_alloc = allocator.get_stats();
        assert!(
            stats_after_alloc.used_pages > 0,
            "Used pages should be greater than 0 after allocations"
        );

        // Get buddy allocator statistics
        let buddy_stats = allocator.get_buddy_stats();
        assert!(
            buddy_stats.total_pages > 0,
            "Buddy total pages should be greater than 0"
        );
    }

    // Deallocate all pages
    for (i, addr) in alloc_addrs.iter().enumerate() {
        let num_pages = match i {
            0 => 1,
            1 => 2,
            2 => 4,
            _ => 1,
        };
        allocator.dealloc_pages(*addr, num_pages);
    }

    // Test memory statistics after deallocation if tracking feature is enabled
    #[cfg(feature = "tracking")]
    {
        let stats_after_dealloc = allocator.get_stats();
        // Note: Used pages might not be exactly 0 due to internal node pool usage
        // but should be significantly reduced
        assert!(
            stats_after_dealloc.used_pages < 100,
            "Used pages should be low after deallocation"
        );
    }

    // Clean up
    dealloc_test_heap(heap_ptr, heap_layout);
}

#[test]
fn test_alloc_dma32_pages_memory_stats() {
    // Allocate actual test memory
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    // Create allocator and set address translator
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    allocator.set_addr_translator(&MOCK_TRANSLATOR);

    // Initialize allocator
    let init_result = allocator.init(heap_addr, TEST_HEAP_SIZE);
    assert!(
        init_result.is_ok(),
        "Failed to initialize allocator: {:?}",
        init_result
    );

    // Test memory statistics if tracking feature is enabled
    #[cfg(feature = "tracking")]
    {
        // Get initial statistics
        let stats_before = allocator.get_stats();
        assert!(
            stats_before.total_pages > 0,
            "Total pages should be greater than 0"
        );
        assert!(
            stats_before.free_pages > 0,
            "Free pages should be greater than 0"
        );
        assert_eq!(
            stats_before.used_pages, 0,
            "Used pages should be 0 initially"
        );

        // Allocate some DMA32 pages
        let result = allocator.alloc_dma32_pages(2, PAGE_SIZE);
        assert!(
            result.is_ok(),
            "Failed to allocate DMA32 pages: {:?}",
            result
        );
        let addr = result.unwrap();

        // Get statistics after allocation
        let stats_after = allocator.get_stats();
        assert_eq!(
            stats_after.used_pages,
            stats_before.used_pages + 2,
            "Used pages should increase by 2"
        );
        assert_eq!(
            stats_after.free_pages,
            stats_before.free_pages - 2,
            "Free pages should decrease by 2"
        );

        // Deallocate the pages
        allocator.dealloc_pages(addr, 2);

        // Get statistics after deallocation
        let stats_final = allocator.get_stats();
        assert_eq!(
            stats_final.used_pages, stats_before.used_pages,
            "Used pages should return to initial value"
        );
        assert_eq!(
            stats_final.free_pages, stats_before.free_pages,
            "Free pages should return to initial value"
        );
    }

    // Clean up
    dealloc_test_heap(heap_ptr, heap_layout);
}

#[test]
fn test_alloc_dma32_pages_multiple_zones() {
    // Allocate two separate memory regions for multiple zones
    let (heap_ptr1, heap_layout1) = alloc_test_heap(TEST_HEAP_SIZE / 2);
    let heap_addr1 = heap_ptr1 as usize;

    let (heap_ptr2, heap_layout2) = alloc_test_heap(TEST_HEAP_SIZE / 2);
    let heap_addr2 = heap_ptr2 as usize;

    // Create allocator and set address translator
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    allocator.set_addr_translator(&MOCK_TRANSLATOR);

    // Initialize allocator with first memory region
    let init_result = allocator.init(heap_addr1, TEST_HEAP_SIZE / 2);
    assert!(
        init_result.is_ok(),
        "Failed to initialize allocator: {:?}",
        init_result
    );

    // Add second memory region as a new zone
    let add_result = allocator.add_memory(heap_addr2, TEST_HEAP_SIZE / 2);
    assert!(
        add_result.is_ok(),
        "Failed to add memory region: {:?}",
        add_result
    );

    // Test allocating from multiple zones
    // First allocation should come from the first zone
    let result1 = allocator.alloc_dma32_pages(1, PAGE_SIZE);
    assert!(
        result1.is_ok(),
        "Failed to allocate 1 page from multiple zones: {:?}",
        result1
    );
    let addr1 = result1.unwrap();
    assert!(
        addr1 >= heap_addr1 || addr1 >= heap_addr2,
        "Allocated address is not in any zone"
    );
    assert!(
        (addr1 < heap_addr1 + TEST_HEAP_SIZE / 2) || (addr1 < heap_addr2 + TEST_HEAP_SIZE / 2),
        "Allocated address is beyond memory end"
    );

    // Second allocation should come from either zone
    let result2 = allocator.alloc_dma32_pages(2, PAGE_SIZE);
    assert!(
        result2.is_ok(),
        "Failed to allocate 2 pages from multiple zones: {:?}",
        result2
    );
    let addr2 = result2.unwrap();
    assert!(
        addr2 >= heap_addr1 || addr2 >= heap_addr2,
        "Allocated address is not in any zone"
    );
    assert!(
        (addr2 < heap_addr1 + TEST_HEAP_SIZE / 2) || (addr2 < heap_addr2 + TEST_HEAP_SIZE / 2),
        "Allocated address is beyond memory end"
    );

    // Clean up
    dealloc_test_heap(heap_ptr1, heap_layout1);
    dealloc_test_heap(heap_ptr2, heap_layout2);
}

#[test]
fn test_alloc_dma32_pages_vs_normal_pages() {
    // Allocate actual test memory
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    // Create allocator and set address translator
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    allocator.set_addr_translator(&MOCK_TRANSLATOR);

    // Initialize allocator
    let init_result = allocator.init(heap_addr, TEST_HEAP_SIZE);
    assert!(
        init_result.is_ok(),
        "Failed to initialize allocator: {:?}",
        init_result
    );

    // Test 1: Allocate DMA32 pages (32-bit memory)
    let result_dma32 = allocator.alloc_dma32_pages(1, PAGE_SIZE);
    assert!(
        result_dma32.is_ok(),
        "Failed to allocate DMA32 pages: {:?}",
        result_dma32
    );
    let addr_dma32 = result_dma32.unwrap();
    assert!(
        addr_dma32 >= heap_addr,
        "Allocated DMA32 address is below memory start"
    );
    assert!(
        addr_dma32 < heap_addr + TEST_HEAP_SIZE,
        "Allocated DMA32 address is beyond memory end"
    );

    // Test 2: Allocate normal pages
    let result_normal = allocator.alloc_pages(1, PAGE_SIZE);
    assert!(
        result_normal.is_ok(),
        "Failed to allocate normal pages: {:?}",
        result_normal
    );
    let addr_normal = result_normal.unwrap();
    assert!(
        addr_normal >= heap_addr,
        "Allocated normal address is below memory start"
    );
    assert!(
        addr_normal < heap_addr + TEST_HEAP_SIZE,
        "Allocated normal address is beyond memory end"
    );

    // Verify both addresses are valid and different
    assert_ne!(
        addr_dma32, addr_normal,
        "DMA32 and normal pages should have different addresses"
    );

    // Test 3: Allocate multiple pages of each type
    let result_dma32_multi = allocator.alloc_dma32_pages(4, PAGE_SIZE);
    assert!(
        result_dma32_multi.is_ok(),
        "Failed to allocate multiple DMA32 pages: {:?}",
        result_dma32_multi
    );

    let result_normal_multi = allocator.alloc_pages(4, PAGE_SIZE);
    assert!(
        result_normal_multi.is_ok(),
        "Failed to allocate multiple normal pages: {:?}",
        result_normal_multi
    );

    // Clean up
    dealloc_test_heap(heap_ptr, heap_layout);
}

#[test]
fn test_alloc_dma32_pages_edge_cases() {
    // Allocate actual test memory
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    // Create allocator and set address translator
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    allocator.set_addr_translator(&MOCK_TRANSLATOR);

    // Initialize allocator
    let init_result = allocator.init(heap_addr, TEST_HEAP_SIZE);
    assert!(
        init_result.is_ok(),
        "Failed to initialize allocator: {:?}",
        init_result
    );

    // Test: Allocate 0 pages
    let result = allocator.alloc_dma32_pages(0, PAGE_SIZE);
    // Note: The behavior for 0 pages may vary - some allocators return 0, others error
    // This test assumes it might succeed (returning 0) or fail, but shouldn't panic
    match result {
        Ok(addr) => assert_eq!(addr, 0, "Expected 0 for 0 pages allocation"),
        Err(_) => {} // Error is also acceptable for 0 pages
    }

    // Clean up
    dealloc_test_heap(heap_ptr, heap_layout);
}

#[test]
fn test_alloc_dma32_pages_stress() {
    // Allocate actual test memory
    let (heap_ptr, heap_layout) = alloc_test_heap(TEST_HEAP_SIZE);
    let heap_addr = heap_ptr as usize;

    // Create allocator and set address translator
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    allocator.set_addr_translator(&MOCK_TRANSLATOR);

    // Initialize allocator
    let init_result = allocator.init(heap_addr, TEST_HEAP_SIZE);
    assert!(
        init_result.is_ok(),
        "Failed to initialize allocator: {:?}",
        init_result
    );

    // Stress test: Allocate and free multiple times
    let mut allocated_addrs = Vec::new();

    // Allocate multiple times
    for i in 0..10 {
        let num_pages = (i % 4) + 1; // 1-4 pages
        let alignment = if i % 2 == 0 { PAGE_SIZE } else { 2 * PAGE_SIZE };

        let result = allocator.alloc_dma32_pages(num_pages, alignment);
        assert!(
            result.is_ok(),
            "Failed to allocate {} pages with alignment {}: {:?}",
            num_pages,
            alignment,
            result
        );
        allocated_addrs.push(result.unwrap());
    }

    // Verify all addresses are valid
    for addr in &allocated_addrs {
        assert!(
            addr >= &heap_addr,
            "Allocated address is below memory start"
        );
        assert!(
            addr < &(heap_addr + TEST_HEAP_SIZE),
            "Allocated address is beyond memory end"
        );
    }

    // Clean up
    dealloc_test_heap(heap_ptr, heap_layout);
}
