//! Benchmarks for SlabByteAllocator - small object allocation
//!
//! This benchmark suite tests the performance and stability of the Slab allocator
//! which is optimized for small object allocations (≤2048 bytes).

use buddy_slab_allocator::{
    BaseAllocator, ByteAllocator, CompositePageAllocator, PageAllocatorForSlab, SlabByteAllocator,
};
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

/// Create initialized slab allocator with page allocator
fn create_slab_allocator(
    heap_ptr: *mut u8,
) -> (
    CompositePageAllocator<PAGE_SIZE>,
    SlabByteAllocator<PAGE_SIZE>,
) {
    let mut page_alloc = CompositePageAllocator::<PAGE_SIZE>::new();
    page_alloc.init(heap_ptr as usize, HEAP_SIZE);

    let mut slab_alloc = SlabByteAllocator::<PAGE_SIZE>::new();
    slab_alloc.init();

    (page_alloc, slab_alloc)
}

/// Benchmark allocations for different size classes
fn bench_size_classes(c: &mut Criterion) {
    let size_classes: [usize; 6] = [8, 64, 512, 1024, 1536, 2048];

    let mut group = c.benchmark_group("slab_size_classes");

    for size in size_classes.iter() {
        let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);
        let (mut page_alloc, mut slab_alloc) = create_slab_allocator(heap_ptr);
        slab_alloc.set_page_allocator(&mut page_alloc as *mut _ as *mut dyn PageAllocatorForSlab);

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, _| {
            let layout = Layout::from_size_align(*size, 8).unwrap();

            b.iter(|| {
                let ptr = slab_alloc.alloc(black_box(layout)).unwrap();
                slab_alloc.dealloc(ptr, layout);
                black_box(ptr)
            });
        });

        dealloc_test_heap(heap_ptr, heap_layout);
    }

    group.finish();
}

/// Benchmark deallocation
fn bench_dealloc(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);
    let (mut page_alloc, mut slab_alloc) = create_slab_allocator(heap_ptr);
    slab_alloc.set_page_allocator(&mut page_alloc as *mut _ as *mut dyn PageAllocatorForSlab);

    c.bench_function("slab_dealloc", |b| {
        let layout = Layout::from_size_align(64, 8).unwrap();

        // Pre-allocate pointers
        let mut pointers = Vec::new();
        for _ in 0..1000 {
            let ptr = slab_alloc.alloc(layout).unwrap();
            pointers.push(ptr);
        }

        b.iter(|| {
            let ptr = pointers.pop().unwrap();
            slab_alloc.dealloc(black_box(ptr), layout);
            // Allocate again to maintain pool
            let new_ptr = slab_alloc.alloc(layout).unwrap();
            pointers.push(new_ptr);
        });

        // Cleanup
        for ptr in pointers {
            slab_alloc.dealloc(ptr, layout);
        }
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

/// Benchmark allocation/deallocation cycle
fn bench_alloc_dealloc_cycle(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);
    let (mut page_alloc, mut slab_alloc) = create_slab_allocator(heap_ptr);
    slab_alloc.set_page_allocator(&mut page_alloc as *mut _ as *mut dyn PageAllocatorForSlab);

    c.bench_function("slab_alloc_dealloc_cycle", |b| {
        b.iter(|| {
            for _ in 0..100 {
                let layout = Layout::from_size_align(64, 8).unwrap();
                let ptr = slab_alloc.alloc(layout).unwrap();
                slab_alloc.dealloc(ptr, layout);
            }
        });
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

/// Benchmark allocations with different alignments
fn bench_alignment(c: &mut Criterion) {
    let alignments = [8, 1024, 2048];

    let mut group = c.benchmark_group("slab_alignment");

    for alignment in alignments.iter() {
        let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);
        let (mut page_alloc, mut slab_alloc) = create_slab_allocator(heap_ptr);
        slab_alloc.set_page_allocator(&mut page_alloc as *mut _ as *mut dyn PageAllocatorForSlab);

        group.bench_with_input(BenchmarkId::from_parameter(alignment), alignment, |b, _| {
            let layout = Layout::from_size_align(64, *alignment).unwrap();

            b.iter(|| {
                let ptr = slab_alloc.alloc(black_box(layout)).unwrap();
                slab_alloc.dealloc(ptr, layout);
                black_box(ptr)
            });
        });

        dealloc_test_heap(heap_ptr, heap_layout);
    }

    group.finish();
}

/// Benchmark random size allocations
fn bench_random_allocations(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);
    let (mut page_alloc, mut slab_alloc) = create_slab_allocator(heap_ptr);
    slab_alloc.set_page_allocator(&mut page_alloc as *mut _ as *mut dyn PageAllocatorForSlab);

    c.bench_function("slab_random_allocations", |b| {
        let mut rng = rand::rngs::SmallRng::from_seed([0; 32]);

        b.iter(|| {
            for _ in 0..100 {
                let size: usize = rng.gen_range(8..2049);
                let size = if size.is_power_of_two() {
                    size
                } else {
                    size.next_power_of_two()
                };
                let layout = Layout::from_size_align(size, 8).unwrap();
                let ptr = slab_alloc.alloc(layout).unwrap();
                slab_alloc.dealloc(ptr, layout);
            }
        });
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

/// Benchmark object pooling - allocate, use, dealloc repeatedly
fn bench_object_pooling(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);
    let (mut page_alloc, mut slab_alloc) = create_slab_allocator(heap_ptr);
    slab_alloc.set_page_allocator(&mut page_alloc as *mut _ as *mut dyn PageAllocatorForSlab);

    c.bench_function("slab_object_pooling", |b| {
        let layout = Layout::from_size_align(128, 8).unwrap();

        // Simulate object pool with fixed size
        let mut pool = Vec::new();
        for _ in 0..100 {
            let ptr = slab_alloc.alloc(layout).unwrap();
            pool.push(ptr);
        }

        b.iter(|| {
            // Get an object from pool, use it, put it back
            let ptr = pool.pop().unwrap();
            // Simulate usage
            black_box(ptr);
            pool.push(ptr);
        });

        // Cleanup
        for ptr in pool {
            slab_alloc.dealloc(ptr, layout);
        }
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

/// Benchmark mixed size allocation pattern
fn bench_mixed_sizes(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);
    let (mut page_alloc, mut slab_alloc) = create_slab_allocator(heap_ptr);
    slab_alloc.set_page_allocator(&mut page_alloc as *mut _ as *mut dyn PageAllocatorForSlab);

    c.bench_function("slab_mixed_sizes", |b| {
        let sizes = [8, 64, 256, 512, 1024, 2048];
        let layouts: Vec<Layout> = sizes
            .iter()
            .map(|&s| Layout::from_size_align(s, 8).unwrap())
            .collect();

        b.iter(|| {
            for layout in &layouts {
                let ptr = slab_alloc.alloc(*layout).unwrap();
                slab_alloc.dealloc(ptr, *layout);
            }
        });
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

/// Benchmark rapid allocation and deallocation stress test
fn bench_stress_test(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);
    let (mut page_alloc, mut slab_alloc) = create_slab_allocator(heap_ptr);
    slab_alloc.set_page_allocator(&mut page_alloc as *mut _ as *mut dyn PageAllocatorForSlab);

    c.bench_function("slab_stress_test", |b| {
        let mut rng = rand::rngs::SmallRng::from_seed([0; 32]);

        b.iter(|| {
            let mut allocated = Vec::new();

            // Stress test: rapid alloc/dealloc with varying sizes
            for _ in 0..1000 {
                if allocated.is_empty() || rng.gen_bool(0.7) {
                    // Allocate
                    let size = rng.gen_range(8..2049);
                    let layout = Layout::from_size_align(size, 8).unwrap();
                    if let Ok(ptr) = slab_alloc.alloc(layout) {
                        allocated.push((ptr, layout));
                    }
                } else {
                    // Deallocate random
                    let idx = rng.gen_range(0..allocated.len());
                    let (ptr, layout) = allocated.swap_remove(idx);
                    slab_alloc.dealloc(ptr, layout);
                }
            }

            // Cleanup
            allocated.clear();
            let ptrs_to_free: Vec<_> = std::mem::take(&mut allocated);
            for (ptr, layout) in ptrs_to_free {
                slab_alloc.dealloc(ptr, layout);
            }
        });
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

/// Benchmark performance under memory pressure
fn bench_memory_pressure(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);
    let (mut page_alloc, mut slab_alloc) = create_slab_allocator(heap_ptr);
    slab_alloc.set_page_allocator(&mut page_alloc as *mut _ as *mut dyn PageAllocatorForSlab);

    c.bench_function("slab_memory_pressure", |b| {
        let layout = Layout::from_size_align(64, 8).unwrap();

        b.iter(|| {
            // Allocate until near capacity
            let mut allocated = Vec::new();
            loop {
                match slab_alloc.alloc(layout) {
                    Ok(ptr) => allocated.push(ptr),
                    Err(_) => break,
                }
            }

            // Free half and reallocate
            for i in (0..allocated.len()).step_by(2) {
                slab_alloc.dealloc(allocated[i], layout);
            }

            // Try to allocate more
            for _ in 0..10 {
                let _ = slab_alloc.alloc(layout);
            }

            // Cleanup
            for ptr in allocated {
                slab_alloc.dealloc(ptr, layout);
            }
        });
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

/// Benchmark statistics retrieval
fn bench_statistics(c: &mut Criterion) {
    let (heap_ptr, heap_layout) = alloc_test_heap(HEAP_SIZE);
    let (mut page_alloc, mut slab_alloc) = create_slab_allocator(heap_ptr);
    slab_alloc.set_page_allocator(&mut page_alloc as *mut _ as *mut dyn PageAllocatorForSlab);

    // Make some allocations
    for _ in 0..10 {
        let layout = Layout::from_size_align(64, 8).unwrap();
        let _ = slab_alloc.alloc(layout);
    }

    c.bench_function("slab_statistics", |b| {
        b.iter(|| {
            let total = slab_alloc.total_bytes();
            let used = slab_alloc.used_bytes();
            let available = slab_alloc.available_bytes();
            black_box((total, used, available))
        });
    });

    dealloc_test_heap(heap_ptr, heap_layout);
}

criterion_group!(
    benches,
    bench_size_classes,
    bench_dealloc,
    bench_alloc_dealloc_cycle,
    bench_alignment,
    bench_random_allocations,
    bench_object_pooling,
    bench_mixed_sizes,
    bench_stress_test,
    bench_memory_pressure,
    bench_statistics
);
criterion_main!(benches);
