//! Benchmarks for GlobalAllocator - the unified allocator interface
//!
//! This benchmark suite tests the performance and stability of the GlobalAllocator
//! which automatically routes small allocations to Slab and large allocations to Buddy.

use buddy_slab_allocator::GlobalAllocator;
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::{Rng, SeedableRng};
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

/// Benchmark small allocations (≤2048 bytes) - uses Slab allocator
fn bench_small_alloc(c: &mut Criterion) {
    let sizes: [usize; 6] = [8, 16, 64, 256, 512, 1024];

    let mut group = c.benchmark_group("global_alloc_small");

    for size in sizes.iter() {
        let layout = Layout::from_size_align(*size, 8).unwrap();
        let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, _| {
            let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
            allocator.init(heap_ptr as usize, HEAP_SIZE).unwrap();

            b.iter(|| {
                let ptr = allocator.alloc(black_box(layout));
                black_box(ptr)
            });
        });

        dealloc_test_heap(heap_ptr, heap_layout);
    }

    group.finish();
}

/// Benchmark large allocations (>2048 bytes) - uses Buddy allocator
fn bench_large_alloc(c: &mut Criterion) {
    let sizes: [usize; 5] = [
        PAGE_SIZE,
        PAGE_SIZE * 2,
        PAGE_SIZE * 4,
        PAGE_SIZE * 8,
        PAGE_SIZE * 16,
    ];

    let mut group = c.benchmark_group("global_alloc_large");

    for size in sizes.iter() {
        let layout = Layout::from_size_align(*size, PAGE_SIZE).unwrap();
        let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, _| {
            let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
            allocator.init(heap_ptr as usize, HEAP_SIZE).unwrap();

            b.iter(|| {
                let ptr = allocator.alloc(black_box(layout));
                black_box(ptr)
            });
        });

        dealloc_test_heap(heap_ptr, heap_layout);
    }

    group.finish();
}

/// Benchmark deallocation for small allocations
fn bench_small_dealloc(c: &mut Criterion) {
    let layout = Layout::from_size_align(64, 8).unwrap();
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

    c.bench_function("global_dealloc_small", |b| {
        let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
        allocator.init(heap_ptr as usize, HEAP_SIZE).unwrap();

        // Pre-allocate a batch of pointers
        let mut pointers = Vec::new();
        for _ in 0..1000 {
            let ptr = allocator.alloc(layout).unwrap();
            pointers.push(ptr);
        }

        b.iter(|| {
            // Release and acquire to keep benchmark going
            let ptr = pointers.pop().unwrap();
            allocator.dealloc(black_box(ptr), layout);
            // Allocate again to maintain pool
            let new_ptr = allocator.alloc(layout).unwrap();
            pointers.push(new_ptr);
        });

        // Cleanup
        for ptr in pointers {
            allocator.dealloc(ptr, layout);
        }
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

/// Benchmark allocation/deallocation cycle
fn bench_alloc_dealloc_cycle(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

    c.bench_function("global_alloc_dealloc_cycle", |b| {
        let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
        allocator.init(heap_ptr as usize, HEAP_SIZE).unwrap();

        b.iter(|| {
            // Simulate realistic usage: allocate and immediately dealloc
            for _ in 0..100 {
                let layout = Layout::from_size_align(64, 8).unwrap();
                let ptr = allocator.alloc(layout).unwrap();
                allocator.dealloc(ptr, layout);
            }
        });
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

/// Benchmark random size allocations
fn bench_random_allocations(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

    c.bench_function("global_random_allocations", |b| {
        let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
        allocator.init(heap_ptr as usize, HEAP_SIZE).unwrap();
        let mut rng = rand::rngs::SmallRng::from_seed([0; 32]);

        b.iter(|| {
            // 100 random allocations
            for _ in 0..100 {
                let size: usize = rng.gen_range(8..2048);
                let size = size.next_power_of_two();
                let layout = Layout::from_size_align(size, 8).unwrap();
                let ptr = allocator.alloc(layout).unwrap();
                allocator.dealloc(ptr, layout);
            }
        });
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

/// Benchmark mixed allocation pattern - simulates real-world usage
fn bench_mixed_pattern(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

    c.bench_function("global_mixed_pattern", |b| {
        let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
        allocator.init(heap_ptr as usize, HEAP_SIZE).unwrap();

        // Pre-allocate a pool of objects
        let mut small_ptrs = Vec::new();
        let mut large_ptrs = Vec::new();

        for _ in 0..100 {
            let small_layout = Layout::from_size_align(64, 8).unwrap();
            small_ptrs.push(allocator.alloc(small_layout).unwrap());
        }

        for _ in 0..10 {
            let large_layout = Layout::from_size_align(PAGE_SIZE, PAGE_SIZE).unwrap();
            large_ptrs.push(allocator.alloc(large_layout).unwrap());
        }

        b.iter(|| {
            // Alternate between small and large allocations
            let small_layout = Layout::from_size_align(64, 8).unwrap();
            let ptr = allocator.alloc(small_layout).unwrap();
            allocator.dealloc(ptr, small_layout);

            let large_layout = Layout::from_size_align(PAGE_SIZE, PAGE_SIZE).unwrap();
            let ptr2 = allocator.alloc(large_layout).unwrap();
            allocator.dealloc(ptr2, large_layout);
        });

        // Cleanup
        let small_layout = Layout::from_size_align(64, 8).unwrap();
        for ptr in small_ptrs {
            allocator.dealloc(ptr, small_layout);
        }
        let large_layout = Layout::from_size_align(PAGE_SIZE, PAGE_SIZE).unwrap();
        for ptr in large_ptrs {
            allocator.dealloc(ptr, large_layout);
        }
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

/// Benchmark page allocation through GlobalAllocator
fn bench_page_allocation(c: &mut Criterion) {
    let page_counts = [1, 2, 4, 8, 16];

    let mut group = c.benchmark_group("global_alloc_pages");

    for num_pages in page_counts.iter() {
        let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);

        group.bench_with_input(BenchmarkId::from_parameter(num_pages), num_pages, |b, _| {
            let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
            allocator.init(heap_ptr as usize, HEAP_SIZE).unwrap();

            b.iter(|| {
                let addr = allocator.alloc_pages(black_box(*num_pages), PAGE_SIZE);
                black_box(addr)
            });
        });

        dealloc_test_heap(heap_ptr, heap_layout);
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_small_alloc,
    bench_large_alloc,
    bench_small_dealloc,
    bench_alloc_dealloc_cycle,
    bench_random_allocations,
    bench_mixed_pattern,
    bench_page_allocation
);
criterion_main!(benches);
