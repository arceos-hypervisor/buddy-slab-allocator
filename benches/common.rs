use criterion::Criterion;
use rand::{rngs::StdRng, SeedableRng};
use std::alloc::{alloc, dealloc, Layout};
use std::time::Duration;

pub const PAGE_SIZE: usize = 0x1000;
pub const HEAP_SIZE: usize = 64 * 1024 * 1024;
pub const OPERATIONS_PER_BATCH: u64 = 256;
const HEAP_ALIGN: usize = 64 * 1024;

pub struct TestHeap {
    ptr: *mut u8,
    layout: Layout,
}

impl TestHeap {
    pub fn new(size: usize) -> Self {
        let layout = Layout::from_size_align(size, HEAP_ALIGN).unwrap();
        let ptr = unsafe { alloc(layout) };
        assert!(!ptr.is_null(), "failed to allocate test heap");
        Self { ptr, layout }
    }

    pub fn addr(&self) -> usize {
        self.ptr as usize
    }
}

impl Drop for TestHeap {
    fn drop(&mut self) {
        unsafe { dealloc(self.ptr, self.layout) };
    }
}

pub fn criterion_config() -> Criterion {
    Criterion::default()
        .warm_up_time(Duration::from_secs(1))
        .measurement_time(Duration::from_secs(5))
        .sample_size(50)
        .noise_threshold(0.05)
}

#[allow(dead_code)]
pub fn seeded_rng() -> StdRng {
    StdRng::from_seed([0; 32])
}
