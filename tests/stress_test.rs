//! Stress tests for allocator stability.

use buddy_slab_allocator::{GlobalAllocator, OsImpl};
use rand::{RngExt, SeedableRng};
use std::alloc::{alloc, dealloc, Layout};
use std::sync::atomic::{AtomicUsize, Ordering};

const PAGE_SIZE: usize = 0x1000;
const HEAP_SIZE: usize = 64 * 1024 * 1024;

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

impl OsImpl for MockOs {
    fn current_cpu_idx(&self) -> usize {
        self.cpu.load(Ordering::Relaxed)
    }
    fn virt_to_phys(&self, vaddr: usize) -> usize {
        vaddr
    }
    fn phys_to_virt(&self, paddr: usize) -> usize {
        paddr
    }
}

static MOCK_OS: MockOs = MockOs::new();

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

fn init_allocator(
    allocator: &GlobalAllocator<PAGE_SIZE>,
    heap: &TestHeap,
    cpu_count: usize,
) {
    MOCK_OS.set_cpu(0);
    unsafe { allocator.init(heap.addr(), HEAP_SIZE, cpu_count, &MOCK_OS).unwrap() };
}

#[test]
#[ignore = "stress test"]
fn stress_random_mixed_alloc_free() {
    let heap = TestHeap::new(HEAP_SIZE);
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    init_allocator(&allocator, &heap, 2);
    let mut rng = rand::rngs::StdRng::from_seed([0; 32]);
    let mut allocated: Vec<(core::ptr::NonNull<u8>, Layout)> = Vec::new();

    for i in 0..10_000 {
        MOCK_OS.set_cpu(i % 2);
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
            unsafe { allocator.dealloc(ptr, layout) };
        }
    }

    for (ptr, layout) in allocated {
        unsafe { allocator.dealloc(ptr, layout) };
    }
}

#[test]
#[ignore = "stress test"]
fn stress_exhaustion_recovery() {
    let heap = TestHeap::new(HEAP_SIZE);
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    init_allocator(&allocator, &heap, 1);
    let layout = Layout::from_size_align(PAGE_SIZE, PAGE_SIZE).unwrap();
    let mut allocated = Vec::new();

    while let Ok(ptr) = allocator.alloc(layout) {
        allocated.push(ptr);
    }

    for ptr in allocated.drain(..allocated.len() / 4) {
        unsafe { allocator.dealloc(ptr, layout) };
    }

    let recovered = allocator.alloc(layout);
    assert!(recovered.is_ok());

    if let Ok(ptr) = recovered {
        unsafe { allocator.dealloc(ptr, layout) };
    }

    for ptr in allocated {
        unsafe { allocator.dealloc(ptr, layout) };
    }
}

#[test]
#[ignore = "stress test"]
fn stress_fragmentation_recovery() {
    let heap = TestHeap::new(HEAP_SIZE);
    let allocator = GlobalAllocator::<PAGE_SIZE>::new();
    init_allocator(&allocator, &heap, 2);
    let small_layout = Layout::from_size_align(64, 8).unwrap();
    let mut small_ptrs = Vec::new();

    for i in 0..4000 {
        MOCK_OS.set_cpu(i % 2);
        if let Ok(ptr) = allocator.alloc(small_layout) {
            small_ptrs.push(ptr);
        }
    }

    for i in (0..small_ptrs.len()).step_by(2) {
        unsafe { allocator.dealloc(small_ptrs[i], small_layout) };
    }

    let large_layout = Layout::from_size_align(PAGE_SIZE * 16, PAGE_SIZE).unwrap();
    let large = allocator.alloc(large_layout);

    for ptr in small_ptrs.into_iter().skip(1).step_by(2) {
        unsafe { allocator.dealloc(ptr, small_layout) };
    }

    if let Ok(ptr) = large {
        unsafe { allocator.dealloc(ptr, large_layout) };
    }
}
