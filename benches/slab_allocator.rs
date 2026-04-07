//! Benchmarks for slab-based small-object allocation paths.

mod common;

use buddy_slab_allocator::{CompositePageAllocator, PageAllocatorForSlab, SlabByteAllocator};
use common::{criterion_config, TestHeap, HEAP_SIZE, OPERATIONS_PER_BATCH, PAGE_SIZE};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::alloc::Layout;
use std::hint::black_box;

struct SlabHarness {
    _heap: TestHeap,
    _page_allocator: Box<CompositePageAllocator<PAGE_SIZE>>,
    slab_allocator: SlabByteAllocator<PAGE_SIZE>,
}

impl SlabHarness {
    fn new() -> Self {
        let heap = TestHeap::new(HEAP_SIZE);
        let mut page_allocator = Box::new(CompositePageAllocator::<PAGE_SIZE>::new());
        page_allocator.init(heap.addr(), HEAP_SIZE);

        let mut slab_allocator = SlabByteAllocator::<PAGE_SIZE>::new();
        slab_allocator.init();
        let page_allocator_ptr = (&mut *page_allocator) as *mut dyn PageAllocatorForSlab;
        slab_allocator.set_page_allocator(page_allocator_ptr);

        Self {
            _heap: heap,
            _page_allocator: page_allocator,
            slab_allocator,
        }
    }
}

fn bench_size_class_alloc_free(c: &mut Criterion) {
    let mut group = c.benchmark_group("slab/size_class_alloc_free");

    for &size in &[8usize, 64, 256, 512, 1024, 2048] {
        group.throughput(Throughput::Bytes(size as u64));
        let mut harness = SlabHarness::new();
        let layout = Layout::from_size_align(size, 8).unwrap();

        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, _| {
            b.iter(|| {
                let ptr = harness.slab_allocator.alloc(black_box(layout)).unwrap();
                harness.slab_allocator.dealloc(ptr, layout);
                black_box(ptr);
            });
        });
    }

    group.finish();
}

fn bench_hot_reuse(c: &mut Criterion) {
    let mut group = c.benchmark_group("slab/hot_reuse");
    group.throughput(Throughput::Elements(1));

    let mut harness = SlabHarness::new();
    let layout = Layout::from_size_align(128, 8).unwrap();

    let ptr = harness.slab_allocator.alloc(layout).unwrap();
    harness.slab_allocator.dealloc(ptr, layout);

    group.bench_function("alloc_free_hot_cache", |b| {
        b.iter(|| {
            let ptr = harness.slab_allocator.alloc(layout).unwrap();
            harness.slab_allocator.dealloc(ptr, layout);
            black_box(ptr);
        });
    });

    group.finish();
}

fn bench_mixed_size_batch(c: &mut Criterion) {
    let mut group = c.benchmark_group("slab/mixed_size_batch");
    let layouts = [
        Layout::from_size_align(8, 8).unwrap(),
        Layout::from_size_align(64, 8).unwrap(),
        Layout::from_size_align(256, 8).unwrap(),
        Layout::from_size_align(512, 8).unwrap(),
        Layout::from_size_align(1024, 8).unwrap(),
        Layout::from_size_align(2048, 8).unwrap(),
    ];
    let total_bytes: usize = layouts.iter().map(Layout::size).sum();
    group.throughput(Throughput::Bytes(total_bytes as u64));

    let mut harness = SlabHarness::new();

    group.bench_function("alloc_free_layout_batch", |b| {
        b.iter(|| {
            for layout in layouts {
                let ptr = harness.slab_allocator.alloc(layout).unwrap();
                harness.slab_allocator.dealloc(ptr, layout);
                black_box(ptr);
            }
        });
    });

    group.finish();
}

fn bench_steady_state(c: &mut Criterion) {
    let mut group = c.benchmark_group("slab/steady_state");
    group.throughput(Throughput::Elements(1));

    let mut harness = SlabHarness::new();
    let layout = Layout::from_size_align(64, 8).unwrap();
    let mut active = Vec::with_capacity(256);

    for _ in 0..256 {
        active.push(harness.slab_allocator.alloc(layout).unwrap());
    }

    group.bench_function("recycle_live_object", |b| {
        b.iter(|| {
            let ptr = active.pop().unwrap();
            harness.slab_allocator.dealloc(ptr, layout);
            let new_ptr = harness.slab_allocator.alloc(layout).unwrap();
            active.push(new_ptr);
            black_box(new_ptr);
        });
    });

    group.finish();
}

fn bench_batch_workload(c: &mut Criterion) {
    let mut group = c.benchmark_group("slab/batch_workload");
    group.throughput(Throughput::Elements(OPERATIONS_PER_BATCH));

    let mut harness = SlabHarness::new();
    let layouts = [
        Layout::from_size_align(8, 8).unwrap(),
        Layout::from_size_align(64, 8).unwrap(),
        Layout::from_size_align(256, 8).unwrap(),
        Layout::from_size_align(1024, 8).unwrap(),
    ];

    group.bench_function("round_robin_layouts", |b| {
        b.iter(|| {
            for idx in 0..OPERATIONS_PER_BATCH as usize {
                let layout = layouts[idx % layouts.len()];
                let ptr = harness.slab_allocator.alloc(layout).unwrap();
                harness.slab_allocator.dealloc(ptr, layout);
                black_box(ptr);
            }
        });
    });

    group.finish();
}

criterion_group! {
    name = benches;
    config = criterion_config();
    targets =
        bench_size_class_alloc_free,
        bench_hot_reuse,
        bench_mixed_size_batch,
        bench_steady_state,
        bench_batch_workload
}
criterion_main!(benches);
