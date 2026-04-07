//! Benchmarks for BuddyPageAllocator - page-level memory allocation
//!
//! This benchmark suite tests the performance and stability of the Buddy allocator
//! which handles page-level allocations with automatic merging.

use buddy_slab_allocator::{BuddyPageAllocator, CompositePageAllocator};
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

/// Benchmark single page allocation
fn bench_single_page_alloc(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

    c.bench_function("buddy_single_page_alloc", |b| {
        let mut allocator = BuddyPageAllocator::<PAGE_SIZE>::new();
        allocator.init(heap_ptr as usize, HEAP_SIZE);

        b.iter(|| {
            let addr = allocator.alloc_pages(black_box(1), PAGE_SIZE);
            black_box(addr)
        });
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

/// Benchmark multiple page allocations
fn bench_multi_page_alloc(c: &mut Criterion) {
    let page_counts = [1, 2, 4, 8, 16, 32, 64];

    let mut group = c.benchmark_group("buddy_multi_page_alloc");

    for num_pages in page_counts.iter() {
        let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

        group.bench_with_input(BenchmarkId::from_parameter(num_pages), num_pages, |b, _| {
            let mut allocator = BuddyPageAllocator::<PAGE_SIZE>::new();
            allocator.init(heap_ptr as usize, HEAP_SIZE);

            b.iter(|| {
                let addr = allocator.alloc_pages(black_box(*num_pages), PAGE_SIZE);
                black_box(addr)
            });
        });

        dealloc_test_heap(heap_ptr, heap_layout);
    }

    group.finish();
}

/// Benchmark deallocation with automatic merging
fn bench_dealloc_with_merge(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

    c.bench_function("buddy_dealloc_with_merge", |b| {
        let mut allocator = BuddyPageAllocator::<PAGE_SIZE>::new();
        allocator.init(heap_ptr as usize, HEAP_SIZE);

        // Pre-allocate multiple buddy blocks that will merge
        let mut addrs = Vec::new();
        for _ in 0..64 {
            let addr = allocator.alloc_pages(1, PAGE_SIZE).unwrap();
            addrs.push(addr);
        }

        b.iter(|| {
            // Deallocate and allocate to test merging efficiency
            let addr = addrs.pop().unwrap();
            allocator.dealloc_pages(black_box(addr), 1);
            // Allocate again to reuse merged blocks
            let new_addr = allocator.alloc_pages(1, PAGE_SIZE);
            addrs.push(new_addr.unwrap());
        });

        // Cleanup remaining allocations
        for addr in addrs {
            allocator.dealloc_pages(addr, 1);
        }
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

/// Benchmark allocation with different alignments
fn bench_alloc_with_alignment(c: &mut Criterion) {
    let alignments = [PAGE_SIZE, PAGE_SIZE * 2, PAGE_SIZE * 4, PAGE_SIZE * 8];

    let mut group = c.benchmark_group("buddy_alloc_with_alignment");

    for alignment in alignments.iter() {
        let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

        group.bench_with_input(BenchmarkId::from_parameter(alignment), alignment, |b, _| {
            let mut allocator = BuddyPageAllocator::<PAGE_SIZE>::new();
            allocator.init(heap_ptr as usize, HEAP_SIZE);

            b.iter(|| {
                let addr = allocator.alloc_pages(black_box(4), black_box(*alignment));
                black_box(addr)
            });
        });

        dealloc_test_heap(heap_ptr, heap_layout);
    }

    group.finish();
}

/// Benchmark fragmentation resistance
fn bench_fragmentation(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

    c.bench_function("buddy_fragmentation", |b| {
        let mut allocator = BuddyPageAllocator::<PAGE_SIZE>::new();
        allocator.init(heap_ptr as usize, HEAP_SIZE);

        b.iter(|| {
            // Allocate many small blocks, then free half
            let mut addrs = Vec::new();
            for _ in 0..512 {
                let addr = allocator.alloc_pages(1, PAGE_SIZE).unwrap();
                addrs.push(addr);
            }

            // Free every other allocation
            for i in (0..512).step_by(2) {
                allocator.dealloc_pages(addrs[i], 1);
            }

            // Try to allocate a large block - should succeed if fragmentation is low
            let large_layout = Layout::from_size_align(PAGE_SIZE * 64, PAGE_SIZE).unwrap();
            let large_addr = allocator.alloc_pages(64, PAGE_SIZE);

            // Cleanup
            if let Ok(addr) = large_addr {
                allocator.dealloc_pages(addr, 64);
            }
            for i in (1..512).step_by(2) {
                allocator.dealloc_pages(addrs[i], 1);
            }
        });
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

/// Benchmark random allocation pattern
fn bench_random_pattern(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

    c.bench_function("buddy_random_pattern", |b| {
        let mut allocator = BuddyPageAllocator::<PAGE_SIZE>::new();
        allocator.init(heap_ptr as usize, HEAP_SIZE);
        let mut rng = rand::rngs::StdRng::from_seed([0; 32]);

        b.iter(|| {
            let mut allocated = Vec::new();

            // Random alloc/dealloc pattern
            for _ in 0..1000 {
                if allocated.is_empty() || rng.random_bool(0.7) {
                    // Allocate
                    let pages = 1 << rng.random_range(0..5); // 1, 2, 4, 8, 16 pages
                    match allocator.alloc_pages(pages, PAGE_SIZE) {
                        Ok(addr) => allocated.push((addr, pages)),
                        Err(_) => break, // Out of memory
                    }
                } else {
                    // Deallocate random item
                    let idx = rng.random_range(0..allocated.len());
                    let (addr, pages) = allocated.swap_remove(idx);
                    allocator.dealloc_pages(addr, pages);
                }
            }

            // Cleanup
            for (addr, pages) in allocated {
                allocator.dealloc_pages(addr, pages);
            }
        });
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

/// Benchmark CompositePageAllocator with contiguous block combination
fn bench_composite_allocator(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

    c.bench_function("composite_allocator", |b| {
        let mut allocator = CompositePageAllocator::<PAGE_SIZE>::new();
        allocator.init(heap_ptr as usize, HEAP_SIZE);

        b.iter(|| {
            // Allocate and deallocate pages
            for _ in 0..100 {
                let addr = allocator.alloc_pages(1, PAGE_SIZE);
                if let Ok(a) = addr {
                    allocator.dealloc_pages(a, 1);
                }
            }
        });
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

/// Benchmark allocate at specific address
fn bench_alloc_at(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

    c.bench_function("buddy_alloc_at", |b| {
        let mut allocator = BuddyPageAllocator::<PAGE_SIZE>::new();
        allocator.init(heap_ptr as usize, HEAP_SIZE);

        // Pre-allocate to create space for specific allocation
        let addr1 = allocator.alloc_pages(1, PAGE_SIZE).unwrap();
        allocator.dealloc_pages(addr1, 1);

        b.iter(|| {
            // Try to allocate at a specific address
            let target = addr1;
            let addr = allocator.alloc_pages_at(black_box(target), 1, PAGE_SIZE);
            black_box(addr)
        });
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

/// Benchmark statistics retrieval
fn bench_statistics(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

    c.bench_function("buddy_statistics", |b| {
        let mut allocator = BuddyPageAllocator::<PAGE_SIZE>::new();
        allocator.init(heap_ptr as usize, HEAP_SIZE);

        // Make some allocations
        for _ in 0..10 {
            let _ = allocator.alloc_pages(1, PAGE_SIZE);
        }

        b.iter(|| {
            let total = allocator.total_pages();
            let used = allocator.used_pages();
            let available = allocator.available_pages();
            black_box((total, used, available))
        });
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

criterion_group!(
    benches,
    bench_single_page_alloc,
    bench_multi_page_alloc,
    bench_dealloc_with_merge,
    bench_alloc_with_alignment,
    bench_fragmentation,
    bench_random_pattern,
    bench_composite_allocator,
    bench_alloc_at,
    bench_statistics
);
criterion_main!(benches);
