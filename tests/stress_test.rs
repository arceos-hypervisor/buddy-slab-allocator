//! Ignored stress tests for allocator stability and long-running behavior.

use buddy_slab_allocator::GlobalAllocator;
use rand::{RngExt, SeedableRng};
use std::alloc::{alloc, dealloc, Layout};

const PAGE_SIZE: usize = 0x1000;
const HEAP_SIZE: usize = 64 * 1024 * 1024;

struct TestHeap {
    ptr: *mut u8,
    layout: Layout,
}

impl TestHeap {
    fn new(size: usize) -> Self {
        let layout = Layout::from_size_align(size, PAGE_SIZE).unwrap();
        let ptr = unsafe { alloc(layout) };
        assert!(!ptr.is_null(), "failed to allocate test heap");
        Self { ptr, layout }
    }

    fn addr(&self) -> usize {
        self.ptr as usize
    }
}

impl Drop for TestHeap {
    fn drop(&mut self) {
        unsafe { dealloc(self.ptr, self.layout) };
    }
}

#[test]
#[ignore = "stress test"]
fn stress_random_mixed_alloc_free() {
    let heap = TestHeap::new(HEAP_SIZE);
    let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
    allocator.init(heap.addr(), HEAP_SIZE).unwrap();
    let mut rng = rand::rngs::StdRng::from_seed([0; 32]);
    let mut allocated = Vec::new();

    for _ in 0..10_000 {
        if allocated.is_empty() || rng.random_bool(0.65) {
            let size: usize = rng.random_range(8..8193);
            let layout = if size <= 2048 {
                Layout::from_size_align(size.next_power_of_two().min(2048), 8).unwrap()
            } else {
                let aligned = size.div_ceil(PAGE_SIZE) * PAGE_SIZE;
                Layout::from_size_align(aligned, PAGE_SIZE).unwrap()
            };

            if let Ok(ptr) = allocator.alloc(layout) {
                allocated.push((ptr, layout));
            }
        } else {
            let idx = rng.random_range(0..allocated.len());
            let (ptr, layout) = allocated.swap_remove(idx);
            allocator.dealloc(ptr, layout);
        }
    }

    for (ptr, layout) in allocated {
        allocator.dealloc(ptr, layout);
    }
}

#[test]
#[ignore = "stress test"]
fn stress_exhaustion_recovery() {
    let heap = TestHeap::new(HEAP_SIZE);
    let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
    allocator.init(heap.addr(), HEAP_SIZE).unwrap();
    let layout = Layout::from_size_align(PAGE_SIZE, PAGE_SIZE).unwrap();
    let mut allocated = Vec::new();

    while let Ok(ptr) = allocator.alloc(layout) {
        allocated.push(ptr);
    }

    assert!(
        !allocated.is_empty(),
        "expected to exhaust heap after allocations"
    );

    for ptr in allocated.drain(..allocated.len() / 4) {
        allocator.dealloc(ptr, layout);
    }

    let recovered = allocator.alloc(layout);
    assert!(
        recovered.is_ok(),
        "allocator should recover after freeing pages"
    );

    if let Ok(ptr) = recovered {
        allocator.dealloc(ptr, layout);
    }

    for ptr in allocated {
        allocator.dealloc(ptr, layout);
    }
}

#[test]
#[ignore = "stress test"]
fn stress_fragmentation_recovery() {
    let heap = TestHeap::new(HEAP_SIZE);
    let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
    allocator.init(heap.addr(), HEAP_SIZE).unwrap();
    let small_layout = Layout::from_size_align(64, 8).unwrap();
    let mut small_ptrs = Vec::new();

    for _ in 0..4000 {
        if let Ok(ptr) = allocator.alloc(small_layout) {
            small_ptrs.push(ptr);
        }
    }

    for i in (0..small_ptrs.len()).step_by(2) {
        allocator.dealloc(small_ptrs[i], small_layout);
    }

    let large_layout = Layout::from_size_align(PAGE_SIZE * 16, PAGE_SIZE).unwrap();
    let large = allocator.alloc(large_layout);

    for ptr in small_ptrs.into_iter().skip(1).step_by(2) {
        allocator.dealloc(ptr, small_layout);
    }

    if let Ok(ptr) = large {
        allocator.dealloc(ptr, large_layout);
    }
}

#[cfg(feature = "tracking")]
#[test]
#[ignore = "stress test"]
fn stress_tracking_invariants() {
    let heap = TestHeap::new(HEAP_SIZE);
    let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();
    allocator.init(heap.addr(), HEAP_SIZE).unwrap();
    let mut rng = rand::rngs::StdRng::from_seed([1; 32]);
    let mut allocated = Vec::new();

    for _ in 0..5000 {
        if allocated.is_empty() || rng.random_bool(0.6) {
            let size: usize = rng.random_range(8..4097);
            let layout = if size <= 2048 {
                Layout::from_size_align(size.next_power_of_two().min(2048), 8).unwrap()
            } else {
                let aligned = size.div_ceil(PAGE_SIZE) * PAGE_SIZE;
                Layout::from_size_align(aligned, PAGE_SIZE).unwrap()
            };

            if let Ok(ptr) = allocator.alloc(layout) {
                allocated.push((ptr, layout));
            }
        } else {
            let idx = rng.random_range(0..allocated.len());
            let (ptr, layout) = allocated.swap_remove(idx);
            allocator.dealloc(ptr, layout);
        }
    }

    for (ptr, layout) in allocated {
        allocator.dealloc(ptr, layout);
    }

    let stats = allocator.get_stats();
    assert!(stats.used_pages <= stats.total_pages);
    assert!(stats.free_pages <= stats.total_pages);
    assert_eq!(stats.used_pages + stats.free_pages, stats.total_pages);
}
