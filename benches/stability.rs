//! Stability and stress testing benchmarks
//!
//! This benchmark suite focuses on stability testing under various stress conditions:
//! - Memory exhaustion handling
//! - Long-running operation stability
//! - Random allocation/deallocation patterns
//! - Fragmentation resistance
//! - Memory leak detection

use buddy_slab_allocator::GlobalAllocator;
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::{RngExt, SeedableRng};
use std::alloc::Layout;
use std::alloc::{alloc, dealloc};

const PAGE_SIZE: usize = 0x1000;
const HEAP_SIZE: usize = 64 * 1024 * 1024; // 64MB

/// Allocate a test heap from the system allocator
fn alloc_test_heap(size: usize) -> (*mut u8, Layout) {
    let layout = Layout::from_size_align(size, PAGE_SIZE).unwrap();
    let ptr = unsafe { alloc(layout) };
    assert!(!ptr.is_null(), "Failed to allocate test heap");
    (ptr, layout)
}

/// Deallocate the test heap
fn dealloc_test_heap(ptr: *mut u8, layout: Layout) {
    unsafe { dealloc(ptr, layout) };
}

/// Stability test: Random allocation/deallocation pattern over many iterations
fn bench_random_pattern_stability(c: &mut Criterion) {
    let iterations = [1000, 5000, 10000];

    let mut group = c.benchmark_group("stability_random_pattern");

    for &iter in iterations.iter() {
        let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

        group.bench_with_input(BenchmarkId::from_parameter(iter), &iter, |b, _| {
            let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
            allocator.init(heap_ptr as usize, HEAP_SIZE).unwrap();
            let mut rng = rand::rngs::StdRng::from_seed([0; 32]);

            b.iter(|| {
                let mut allocated = Vec::new();

                for _ in 0..iter {
                    if allocated.is_empty() || rng.random_bool(0.6) {
                        // 60% allocate
                        let size = rng.random_range(8..8193);
                        let size = if size <= 2048 {
                            size
                        } else {
                            // Align to page size for large allocations
                            ((size + PAGE_SIZE - 1) / PAGE_SIZE) * PAGE_SIZE
                        };
                        let layout = Layout::from_size_align(size, 8).unwrap();
                        if let Ok(ptr) = allocator.alloc(layout) {
                            allocated.push((ptr, layout));
                        }
                    } else {
                        // 40% deallocate
                        let idx = rng.random_range(0..allocated.len());
                        let (ptr, layout) = allocated.swap_remove(idx);
                        allocator.dealloc(ptr, layout);
                    }
                }

                // Cleanup - verify no leaks by checking stats
                #[cfg(feature = "tracking")]
                {
                    let before = allocator.get_stats();
                }

                for (ptr, layout) in allocated {
                    allocator.dealloc(ptr, layout);
                }

                #[cfg(feature = "tracking")]
                {
                    let after = allocator.get_stats();
                    // Verify we're back to initial state
                    assert_eq!(after.used_pages, 0, "Memory leak detected!");
                }
            });
        });

        dealloc_test_heap(heap_ptr, heap_layout);
    }

    group.finish();
}

/// Stability test: Allocate to exhaustion and handle gracefully
fn bench_exhaustion_handling(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

    c.bench_function("stability_exhaustion", |b| {
        let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
        allocator.init(heap_ptr as usize, HEAP_SIZE).unwrap();

        b.iter(|| {
            let mut allocated = Vec::new();
            let layout = Layout::from_size_align(PAGE_SIZE, PAGE_SIZE).unwrap();

            // Allocate until exhaustion
            loop {
                match allocator.alloc(layout) {
                    Ok(ptr) => allocated.push(ptr),
                    Err(_) => break, // Expected - out of memory
                }
            }

            // Verify we can still deallocate
            for ptr in allocated.iter().take(10) {
                allocator.dealloc(*ptr, layout);
            }

            // Verify we can allocate again after freeing
            let new_ptr = allocator.alloc(layout);
            assert!(new_ptr.is_ok(), "Failed to allocate after freeing memory");

            // Cleanup
            if let Ok(ptr) = new_ptr {
                allocator.dealloc(ptr, layout);
            }
            for ptr in allocated {
                allocator.dealloc(ptr, layout);
            }
        });
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

/// Stability test: Fragmentation resistance
fn bench_fragmentation_resistance(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

    c.bench_function("stability_fragmentation", |b| {
        let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
        allocator.init(heap_ptr as usize, HEAP_SIZE).unwrap();

        b.iter(|| {
            let mut small_ptrs = Vec::new();
            let small_layout = Layout::from_size_align(64, 8).unwrap();

            // Allocate many small objects
            for _ in 0..1000 {
                if let Ok(ptr) = allocator.alloc(small_layout) {
                    small_ptrs.push(ptr);
                }
            }

            // Free every other one to create fragmentation
            for i in (0..small_ptrs.len()).step_by(2) {
                allocator.dealloc(small_ptrs[i], small_layout);
            }

            // Try to allocate a large contiguous block
            let large_layout = Layout::from_size_align(PAGE_SIZE * 16, PAGE_SIZE).unwrap();
            let large_ptr = allocator.alloc(large_layout);

            // Cleanup
            for ptr in small_ptrs {
                allocator.dealloc(ptr, small_layout);
            }
            if let Ok(ptr) = large_ptr {
                allocator.dealloc(ptr, large_layout);
            }
        });
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

/// Stability test: Alternating allocation/deallocation pattern
fn bench_alternating_pattern(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

    c.bench_function("stability_alternating", |b| {
        let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
        allocator.init(heap_ptr as usize, HEAP_SIZE).unwrap();

        b.iter(|| {
            let mut ptrs = Vec::new();

            // Alternating allocate/dealloc pattern
            for i in 0..500 {
                if i % 2 == 0 {
                    let layout = Layout::from_size_align(64, 8).unwrap();
                    if let Ok(ptr) = allocator.alloc(layout) {
                        ptrs.push((ptr, layout));
                    }
                } else if !ptrs.is_empty() {
                    let (ptr, layout) = ptrs.remove(0);
                    allocator.dealloc(ptr, layout);
                }
            }

            // Cleanup
            for (ptr, layout) in ptrs {
                allocator.dealloc(ptr, layout);
            }
        });
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

/// Stability test: Long-running operation with periodic checks
fn bench_long_running(c: &mut Criterion) {
    let durations = [1000, 5000, 10000];

    let mut group = c.benchmark_group("stability_long_running");

    for &duration in durations.iter() {
        let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

        group.bench_with_input(BenchmarkId::from_parameter(duration), &duration, |b, _| {
            let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
            allocator.init(heap_ptr as usize, HEAP_SIZE).unwrap();
            let mut rng = rand::rngs::StdRng::from_seed([0; 32]);

            b.iter(|| {
                for _ in 0..duration {
                    let size = rng.random_range(8..2049);
                    let layout = Layout::from_size_align(size, 8).unwrap();
                    let ptr = allocator.alloc(layout);

                    if let Ok(p) = ptr {
                        allocator.dealloc(p, layout);
                    }
                }

                #[cfg(feature = "tracking")]
                {
                    let stats = allocator.get_stats();
                    // Verify stats are consistent
                    assert!(stats.used_pages <= stats.total_pages);
                    assert!(stats.free_pages <= stats.total_pages);
                    assert_eq!(stats.used_pages + stats.free_pages, stats.total_pages);
                }
            });
        });

        dealloc_test_heap(heap_ptr, heap_layout);
    }

    group.finish();
}

/// Stress test: Rapid allocation/deallocation of mixed sizes
fn bench_rapid_mixed_sizes(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

    c.bench_function("stress_rapid_mixed", |b| {
        let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
        allocator.init(heap_ptr as usize, HEAP_SIZE).unwrap();
        let mut rng = rand::rngs::StdRng::from_seed([0; 32]);

        b.iter(|| {
            let mut allocated = Vec::new();

            // Rapid mixed-size allocations
            for _ in 0..5000 {
                let size = rng.random_range(8..16385);
                let aligned_size = if size <= 2048 {
                    size
                } else {
                    ((size + PAGE_SIZE - 1) / PAGE_SIZE) * PAGE_SIZE
                };
                let layout = Layout::from_size_align(aligned_size, 8).unwrap();

                if let Ok(ptr) = allocator.alloc(layout) {
                    if rng.random_bool(0.5) {
                        // Immediately free 50% of allocations
                        allocator.dealloc(ptr, layout);
                    } else {
                        allocated.push((ptr, layout));
                    }
                }
            }

            // Cleanup
            for (ptr, layout) in allocated {
                allocator.dealloc(ptr, layout);
            }
        });
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

/// Stress test: Page allocation pressure
fn bench_page_allocation_pressure(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

    c.bench_function("stress_page_pressure", |b| {
        let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
        allocator.init(heap_ptr as usize, HEAP_SIZE).unwrap();

        b.iter(|| {
            let mut page_addrs = Vec::new();

            // Allocate pages until near exhaustion
            loop {
                match allocator.alloc_pages(1, PAGE_SIZE) {
                    Ok(addr) => page_addrs.push(addr),
                    Err(_) => break,
                }
            }

            // Free and reallocate in different patterns
            for i in (0..page_addrs.len()).step_by(2) {
                allocator.dealloc_pages(page_addrs[i], 1);
            }

            // Try to allocate more
            let mut new_addrs = Vec::new();
            for _ in 0..5 {
                if let Ok(addr) = allocator.alloc_pages(1, PAGE_SIZE) {
                    new_addrs.push(addr);
                }
            }

            // Cleanup
            for addr in page_addrs {
                allocator.dealloc_pages(addr, 1);
            }
            for addr in new_addrs {
                allocator.dealloc_pages(addr, 1);
            }
        });
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

/// Memory leak detection test
fn bench_memory_leak_detection(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

    c.bench_function("stability_leak_detection", |b| {
        let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
        allocator.init(heap_ptr as usize, HEAP_SIZE).unwrap();

        #[cfg(feature = "tracking")]
        {
            let initial_stats = allocator.get_stats();
        }

        b.iter(|| {
            let mut ptrs = Vec::new();
            let mut rng = rand::rngs::StdRng::from_seed([0; 32]);

            // Perform random allocations
            for _ in 0..1000 {
                let size = rng.random_range(8..2049);
                let layout = Layout::from_size_align(size, 8).unwrap();
                if let Ok(ptr) = allocator.alloc(layout) {
                    ptrs.push((ptr, layout));
                }
            }

            // Free all allocations
            for (ptr, layout) in &ptrs {
                allocator.dealloc(*ptr, *layout);
            }

            #[cfg(feature = "tracking")]
            {
                let stats = allocator.get_stats();
                // Verify no memory leaks
                assert_eq!(stats.used_pages, 0, "Memory leak detected!");
            }

            ptrs.clear();
        });
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

/// Stability test: Edge cases
fn bench_edge_cases(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

    c.bench_function("stability_edge_cases", |b| {
        let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
        allocator.init(heap_ptr as usize, HEAP_SIZE).unwrap();

        b.iter(|| {
            // Test minimum size allocation
            let min_layout = Layout::from_size_align(1, 1).unwrap();
            let min_ptr = allocator.alloc(min_layout);
            if let Ok(ptr) = min_ptr {
                allocator.dealloc(ptr, min_layout);
            }

            // Test maximum small size allocation
            let max_small_layout = Layout::from_size_align(2048, 2048).unwrap();
            let max_small_ptr = allocator.alloc(max_small_layout);
            if let Ok(ptr) = max_small_ptr {
                allocator.dealloc(ptr, max_small_layout);
            }

            // Test page-aligned allocation
            let page_layout = Layout::from_size_align(PAGE_SIZE, PAGE_SIZE).unwrap();
            let page_ptr = allocator.alloc(page_layout);
            if let Ok(ptr) = page_ptr {
                allocator.dealloc(ptr, page_layout);
            }

            // Test odd alignment - alignment must be power of two
            let odd_align = 8; // Changed from 7 to 8 (power of 2)
            let odd_layout = Layout::from_size_align(64, odd_align).unwrap();
            let odd_ptr = allocator.alloc(odd_layout);
            if let Ok(ptr) = odd_ptr {
                allocator.dealloc(ptr, odd_layout);
            }
        });
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

criterion_group!(
    benches,
    bench_random_pattern_stability,
    bench_exhaustion_handling,
    bench_fragmentation_resistance,
    bench_alternating_pattern,
    bench_long_running,
    bench_rapid_mixed_sizes,
    bench_page_allocation_pressure,
    bench_memory_leak_detection,
    bench_edge_cases
);
criterion_main!(benches);
