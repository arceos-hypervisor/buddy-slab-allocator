//! Benchmarks for the unified global allocator API.

mod common;

use buddy_slab_allocator::{GlobalAllocator, Os};
use common::{criterion_config, TestHeap, HEAP_SIZE, OPERATIONS_PER_BATCH, PAGE_SIZE};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use spin::Mutex;
use std::alloc::{alloc, dealloc, Layout};
use std::hint::black_box;
use std::sync::atomic::{AtomicUsize, Ordering};

struct MockOs {
    cpu: AtomicUsize,
}

impl MockOs {
    const fn new() -> Self {
        Self {
            cpu: AtomicUsize::new(0),
        }
    }

    fn set_cpu(&self, cpu: usize) {
        self.cpu.store(cpu, Ordering::Relaxed);
    }
}

impl Os for MockOs {
    fn current_cpu_idx(&self) -> usize {
        self.cpu.load(Ordering::Relaxed)
    }
}

static MOCK_OS: MockOs = MockOs::new();

struct MetadataBuf {
    ptr: *mut u8,
    layout: Layout,
}

impl MetadataBuf {
    fn new(cpu_count: usize) -> Self {
        let size = GlobalAllocator::<PAGE_SIZE>::required_metadata_size(cpu_count);
        let layout = Layout::from_size_align(size, PAGE_SIZE).unwrap();
        let ptr = unsafe { alloc(layout) };
        assert!(!ptr.is_null(), "failed to allocate metadata");
        Self { ptr, layout }
    }
}

impl Drop for MetadataBuf {
    fn drop(&mut self) {
        unsafe { dealloc(self.ptr, self.layout) };
    }
}

struct GlobalHarness {
    _heap: TestHeap,
    _meta: MetadataBuf,
    allocator: GlobalAllocator<PAGE_SIZE>,
}

impl GlobalHarness {
    fn new(cpu_count: usize) -> Self {
        let heap = TestHeap::new(HEAP_SIZE);
        let meta = MetadataBuf::new(cpu_count);
        let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
        unsafe {
            allocator
                .init(
                    meta.ptr as usize,
                    meta.layout.size(),
                    heap.addr(),
                    HEAP_SIZE,
                    cpu_count,
                    &MOCK_OS,
                )
                .unwrap();
        }
        Self {
            _heap: heap,
            _meta: meta,
            allocator,
        }
    }
}

fn bench_small_alloc_free(c: &mut Criterion) {
    let mut group = c.benchmark_group("global/small_alloc_free");

    for &size in &[8usize, 64, 512, 2048] {
        group.throughput(Throughput::Bytes(size as u64));
        let harness = Mutex::new(GlobalHarness::new(2));
        let layout = Layout::from_size_align(size, 8).unwrap();

        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, _| {
            b.iter(|| {
                MOCK_OS.set_cpu(0);
                let guard = harness.lock();
                let ptr = guard.allocator.alloc(black_box(layout)).unwrap();
                guard.allocator.dealloc(ptr, layout);
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
        let harness = Mutex::new(GlobalHarness::new(2));
        let layout = Layout::from_size_align(size, PAGE_SIZE).unwrap();

        group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, _| {
            b.iter(|| {
                let guard = harness.lock();
                let ptr = guard.allocator.alloc(black_box(layout)).unwrap();
                guard.allocator.dealloc(ptr, layout);
                black_box(ptr);
            });
        });
    }

    group.finish();
}

fn bench_mixed_workload(c: &mut Criterion) {
    let mut group = c.benchmark_group("global/mixed_workload");
    group.throughput(Throughput::Elements(OPERATIONS_PER_BATCH));

    let harness = Mutex::new(GlobalHarness::new(2));
    let layouts = [
        Layout::from_size_align(64, 8).unwrap(),
        Layout::from_size_align(256, 8).unwrap(),
        Layout::from_size_align(PAGE_SIZE, PAGE_SIZE).unwrap(),
        Layout::from_size_align(PAGE_SIZE * 4, PAGE_SIZE).unwrap(),
    ];

    group.bench_function("alternating_small_and_large", |b| {
        b.iter(|| {
            for idx in 0..OPERATIONS_PER_BATCH as usize {
                MOCK_OS.set_cpu(idx % 2);
                let layout = layouts[idx % layouts.len()];
                let guard = harness.lock();
                let ptr = guard.allocator.alloc(layout).unwrap();
                guard.allocator.dealloc(ptr, layout);
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
        let harness = Mutex::new(GlobalHarness::new(2));

        group.bench_with_input(
            BenchmarkId::from_parameter(num_pages),
            &num_pages,
            |b, &pages| {
                b.iter(|| {
                    let guard = harness.lock();
                    let addr = guard
                        .allocator
                        .alloc_pages(black_box(pages), PAGE_SIZE)
                        .unwrap();
                    guard.allocator.dealloc_pages(addr, pages);
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
