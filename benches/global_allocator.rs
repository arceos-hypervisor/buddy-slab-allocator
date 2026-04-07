//! Benchmarks for the unified global allocator API.

mod common;

use buddy_slab_allocator::GlobalAllocator;
use common::{criterion_config, TestHeap, HEAP_SIZE, OPERATIONS_PER_BATCH, PAGE_SIZE};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::alloc::Layout;
use std::hint::black_box;

struct GlobalHarness {
    _heap: TestHeap,
    allocator: Box<GlobalAllocator<PAGE_SIZE>>,
}

impl GlobalHarness {
    fn new() -> Self {
        let heap = TestHeap::new(HEAP_SIZE);
        let mut allocator = Box::new(GlobalAllocator::<PAGE_SIZE>::new());
        allocator.init(heap.addr(), HEAP_SIZE).unwrap();
        Self {
            _heap: heap,
            allocator,
        }
    }
}

fn bench_small_alloc_free(c: &mut Criterion) {
    let mut group = c.benchmark_group("global/small_alloc_free");

    for &size in &[8usize, 64, 512, 2048] {
        group.throughput(Throughput::Bytes(size as u64));
        let mut harness = GlobalHarness::new();
        let layout = Layout::from_size_align(size, 8).unwrap();

        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, _| {
            b.iter(|| {
                let ptr = harness.allocator.alloc(black_box(layout)).unwrap();
                harness.allocator.dealloc(ptr, layout);
                black_box(ptr);
            });
        });
    }

    group.finish();
}

fn bench_large_alloc_free(c: &mut Criterion) {
    let mut group = c.benchmark_group("global/large_alloc_free");

    for &size in &[PAGE_SIZE, PAGE_SIZE * 4, PAGE_SIZE * 16] {
        group.throughput(Throughput::Bytes(size as u64));
        let mut harness = GlobalHarness::new();
        let layout = Layout::from_size_align(size, PAGE_SIZE).unwrap();

        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, _| {
            b.iter(|| {
                let ptr = harness.allocator.alloc(black_box(layout)).unwrap();
                harness.allocator.dealloc(ptr, layout);
                black_box(ptr);
            });
        });
    }

    group.finish();
}

fn bench_mixed_workload(c: &mut Criterion) {
    let mut group = c.benchmark_group("global/mixed_workload");
    group.throughput(Throughput::Elements(OPERATIONS_PER_BATCH));

    let mut harness = GlobalHarness::new();
    let layouts = [
        Layout::from_size_align(64, 8).unwrap(),
        Layout::from_size_align(256, 8).unwrap(),
        Layout::from_size_align(PAGE_SIZE, PAGE_SIZE).unwrap(),
        Layout::from_size_align(PAGE_SIZE * 4, PAGE_SIZE).unwrap(),
    ];

    group.bench_function("alternating_small_and_large", |b| {
        b.iter(|| {
            for idx in 0..OPERATIONS_PER_BATCH as usize {
                let layout = layouts[idx % layouts.len()];
                let ptr = harness.allocator.alloc(layout).unwrap();
                harness.allocator.dealloc(ptr, layout);
                black_box(ptr);
            }
        });
    });

    group.finish();
}

fn bench_page_interface(c: &mut Criterion) {
    let mut group = c.benchmark_group("global/page_interface");

    for &num_pages in &[1usize, 4, 16, 64] {
        group.throughput(Throughput::Bytes((num_pages * PAGE_SIZE) as u64));
        let mut harness = GlobalHarness::new();

        group.bench_with_input(
            BenchmarkId::from_parameter(num_pages),
            &num_pages,
            |b, &pages| {
                b.iter(|| {
                    let addr = harness
                        .allocator
                        .alloc_pages(black_box(pages), PAGE_SIZE)
                        .unwrap();
                    harness.allocator.dealloc_pages(addr, pages);
                    black_box(addr);
                });
            },
        );
    }

    group.finish();
}

criterion_group! {
    name = benches;
    config = criterion_config();
    targets =
        bench_small_alloc_free,
        bench_large_alloc_free,
        bench_mixed_workload,
        bench_page_interface
}
criterion_main!(benches);
