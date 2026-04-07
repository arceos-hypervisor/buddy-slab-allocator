//! Benchmarks for buddy-based page allocation paths.

mod common;

use buddy_slab_allocator::{BuddyPageAllocator, CompositePageAllocator};
use common::{criterion_config, seeded_rng, TestHeap, HEAP_SIZE, OPERATIONS_PER_BATCH, PAGE_SIZE};
use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion, Throughput};
use rand::RngExt;
use std::hint::black_box;

fn bench_page_alloc_free(c: &mut Criterion) {
    let mut group = c.benchmark_group("buddy/page_alloc_free");

    for &num_pages in &[1usize, 2, 4, 16, 64] {
        group.throughput(Throughput::Bytes((num_pages * PAGE_SIZE) as u64));
        let heap = TestHeap::new(HEAP_SIZE);
        let mut allocator = BuddyPageAllocator::<PAGE_SIZE>::new();
        allocator.init(heap.addr(), HEAP_SIZE);

        group.bench_with_input(
            BenchmarkId::from_parameter(num_pages),
            &num_pages,
            |b, &pages| {
                b.iter(|| {
                    let addr = allocator.alloc_pages(black_box(pages), PAGE_SIZE).unwrap();
                    allocator.dealloc_pages(addr, pages);
                    black_box(addr);
                });
            },
        );
    }

    group.finish();
}

fn bench_alignment_alloc_free(c: &mut Criterion) {
    let mut group = c.benchmark_group("buddy/alignment_alloc_free");

    for &alignment in &[PAGE_SIZE, PAGE_SIZE * 2, PAGE_SIZE * 4] {
        group.throughput(Throughput::Bytes((4 * PAGE_SIZE) as u64));
        let heap = TestHeap::new(HEAP_SIZE);
        let mut allocator = BuddyPageAllocator::<PAGE_SIZE>::new();
        allocator.init(heap.addr(), HEAP_SIZE);

        group.bench_with_input(
            BenchmarkId::from_parameter(alignment),
            &alignment,
            |b, &align| {
                b.iter(|| {
                    let addr = allocator
                        .alloc_pages(black_box(4), black_box(align))
                        .unwrap();
                    allocator.dealloc_pages(addr, 4);
                    black_box(addr);
                });
            },
        );
    }

    group.finish();
}

fn bench_fragmentation_recovery(c: &mut Criterion) {
    let mut group = c.benchmark_group("buddy/fragmentation_recovery");
    group.throughput(Throughput::Bytes((64 * PAGE_SIZE) as u64));

    group.bench_function("alloc_large_after_fragmentation", |b| {
        b.iter_batched_ref(
            || {
                let heap = TestHeap::new(HEAP_SIZE);
                let mut allocator = BuddyPageAllocator::<PAGE_SIZE>::new();
                allocator.init(heap.addr(), HEAP_SIZE);

                let mut addrs = Vec::with_capacity(512);
                for _ in 0..512 {
                    addrs.push(allocator.alloc_pages(1, PAGE_SIZE).unwrap());
                }

                (heap, allocator, addrs)
            },
            |(_, allocator, addrs)| {
                for i in (0..addrs.len()).step_by(2) {
                    allocator.dealloc_pages(addrs[i], 1);
                }

                let large = allocator.alloc_pages(64, PAGE_SIZE).unwrap();
                allocator.dealloc_pages(large, 64);

                for i in (1..addrs.len()).step_by(2) {
                    allocator.dealloc_pages(addrs[i], 1);
                }

                black_box(large);
            },
            BatchSize::SmallInput,
        );
    });

    group.finish();
}

fn bench_random_workload(c: &mut Criterion) {
    let mut group = c.benchmark_group("buddy/random_workload");
    group.throughput(Throughput::Elements(OPERATIONS_PER_BATCH));

    group.bench_function("mixed_alloc_free_batch", |b| {
        b.iter_batched_ref(
            || {
                let heap = TestHeap::new(HEAP_SIZE);
                let mut allocator = BuddyPageAllocator::<PAGE_SIZE>::new();
                allocator.init(heap.addr(), HEAP_SIZE);
                (heap, allocator)
            },
            |(_, allocator)| {
                let mut rng = seeded_rng();
                let mut allocated = Vec::new();

                for _ in 0..OPERATIONS_PER_BATCH {
                    if allocated.is_empty() || rng.random_bool(0.65) {
                        let pages = 1usize << rng.random_range(0..=4);
                        if let Ok(addr) = allocator.alloc_pages(pages, PAGE_SIZE) {
                            allocated.push((addr, pages));
                        }
                    } else {
                        let idx = rng.random_range(0..allocated.len());
                        let (addr, pages) = allocated.swap_remove(idx);
                        allocator.dealloc_pages(addr, pages);
                    }
                }

                for (addr, pages) in allocated {
                    allocator.dealloc_pages(addr, pages);
                }
            },
            BatchSize::SmallInput,
        );
    });

    group.finish();
}

fn bench_composite_non_power_of_two(c: &mut Criterion) {
    let mut group = c.benchmark_group("buddy/composite_non_power_of_two");

    for &num_pages in &[3usize, 5, 9] {
        group.throughput(Throughput::Bytes((num_pages * PAGE_SIZE) as u64));
        let heap = TestHeap::new(HEAP_SIZE);
        let mut allocator = CompositePageAllocator::<PAGE_SIZE>::new();
        allocator.init(heap.addr(), HEAP_SIZE);

        group.bench_with_input(
            BenchmarkId::from_parameter(num_pages),
            &num_pages,
            |b, &pages| {
                b.iter(|| {
                    let addr = allocator.alloc_pages(pages, PAGE_SIZE).unwrap();
                    allocator.dealloc_pages(addr, pages);
                    black_box(addr);
                });
            },
        );
    }

    group.finish();
}

fn bench_statistics_query(c: &mut Criterion) {
    let mut group = c.benchmark_group("buddy/statistics_query");
    group.throughput(Throughput::Elements(3));

    let heap = TestHeap::new(HEAP_SIZE);
    let mut allocator = BuddyPageAllocator::<PAGE_SIZE>::new();
    allocator.init(heap.addr(), HEAP_SIZE);

    for _ in 0..64 {
        let addr = allocator.alloc_pages(1, PAGE_SIZE).unwrap();
        allocator.dealloc_pages(addr, 1);
    }

    group.bench_function("page_counters", |b| {
        b.iter(|| {
            let snapshot = (
                allocator.total_pages(),
                allocator.used_pages(),
                allocator.available_pages(),
            );
            black_box(snapshot);
        });
    });

    group.finish();
}

criterion_group! {
    name = benches;
    config = criterion_config();
    targets =
        bench_page_alloc_free,
        bench_alignment_alloc_free,
        bench_fragmentation_recovery,
        bench_random_workload,
        bench_composite_non_power_of_two,
        bench_statistics_query
}
criterion_main!(benches);
