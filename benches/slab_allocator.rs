//! Benchmarks for slab-based small-object allocation paths.

mod common;

use buddy_slab_allocator::{
    CompositePageAllocator, SlabAllocDecision, SlabByteAllocator, SlabDeallocDecision,
};
use common::{criterion_config, TestHeap, HEAP_SIZE, OPERATIONS_PER_BATCH, PAGE_SIZE};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::alloc::Layout;
use std::hint::black_box;

struct SlabHarness {
    _heap: TestHeap,
    page_allocator: CompositePageAllocator<PAGE_SIZE>,
    slab_allocator: SlabByteAllocator<PAGE_SIZE>,
}

impl SlabHarness {
    fn new() -> Self {
        let heap = TestHeap::new(HEAP_SIZE);
        let mut page_allocator = CompositePageAllocator::<PAGE_SIZE>::new();
        page_allocator.init(heap.addr(), HEAP_SIZE);

        Self {
            _heap: heap,
            page_allocator,
            slab_allocator: SlabByteAllocator::new(),
        }
    }

    fn alloc_small(&mut self, layout: Layout) -> core::ptr::NonNull<u8> {
        loop {
            match self.slab_allocator.alloc(layout).unwrap() {
                SlabAllocDecision::Allocated(ptr, _) => return ptr,
                SlabAllocDecision::NeedsRefill {
                    size_class,
                    page_count,
                    slab_bytes,
                } => {
                    let slab_base = self
                        .page_allocator
                        .alloc_pages(page_count, slab_bytes)
                        .unwrap();
                    self.slab_allocator
                        .provide_slab(size_class, 0, slab_base, slab_bytes)
                        .unwrap();
                }
            }
        }
    }

    fn dealloc_small(&mut self, ptr: core::ptr::NonNull<u8>, layout: Layout) {
        if let SlabDeallocDecision::ReleaseSlab {
            slab_base,
            page_count,
            ..
        } = self.slab_allocator.dealloc(ptr, layout)
        {
            self.page_allocator.dealloc_pages(slab_base, page_count);
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
                let ptr = harness.alloc_small(black_box(layout));
                harness.dealloc_small(ptr, layout);
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
    let ptr = harness.alloc_small(layout);
    harness.dealloc_small(ptr, layout);

    group.bench_function("alloc_free_hot_cache", |b| {
        b.iter(|| {
            let ptr = harness.alloc_small(layout);
            harness.dealloc_small(ptr, layout);
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
                let ptr = harness.alloc_small(layout);
                harness.dealloc_small(ptr, layout);
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
        active.push(harness.alloc_small(layout));
    }

    group.bench_function("recycle_live_object", |b| {
        b.iter(|| {
            let ptr = active.pop().unwrap();
            harness.dealloc_small(ptr, layout);
            let new_ptr = harness.alloc_small(layout);
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
                let ptr = harness.alloc_small(layout);
                harness.dealloc_small(ptr, layout);
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
