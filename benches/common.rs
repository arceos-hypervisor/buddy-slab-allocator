#![allow(dead_code)]

use buddy_slab_allocator::{BuddyAllocator, GlobalAllocator, OsImpl, SlabAllocResult, SlabAllocator, SlabDeallocResult};
use core::alloc::Layout;
use rand::{rngs::StdRng, SeedableRng};
use std::alloc::{alloc, dealloc};
use std::sync::atomic::{AtomicUsize, Ordering};

pub const PAGE_SIZE: usize = 0x1000;
pub const HEAP_SIZE: usize = 64 * 1024 * 1024;
pub const OPERATIONS_PER_BATCH: usize = 256;
pub const FRAGMENTATION_PAGES: usize = 512;

const REGION_ALIGN: usize = 64 * 1024;

pub struct HostRegion {
    ptr: *mut u8,
    layout: Layout,
}

impl HostRegion {
    pub fn new(size: usize) -> Self {
        let layout = Layout::from_size_align(size, REGION_ALIGN).unwrap();
        let ptr = unsafe { alloc(layout) };
        assert!(!ptr.is_null(), "failed to allocate host region");
        Self { ptr, layout }
    }

    pub fn addr(&self) -> usize {
        self.ptr as usize
    }

    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        unsafe { core::slice::from_raw_parts_mut(self.ptr, self.layout.size()) }
    }
}

impl Drop for HostRegion {
    fn drop(&mut self) {
        unsafe { dealloc(self.ptr, self.layout) };
    }
}

pub struct MockOs {
    cpu: AtomicUsize,
}

impl MockOs {
    pub const fn new() -> Self {
        Self {
            cpu: AtomicUsize::new(0),
        }
    }

    pub fn set_cpu(&self, cpu: usize) {
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
}

pub static MOCK_OS: MockOs = MockOs::new();

pub fn seeded_rng() -> StdRng {
    StdRng::from_seed([0; 32])
}

pub struct BuddyHarness {
    _region: HostRegion,
    pub allocator: BuddyAllocator<PAGE_SIZE>,
}

impl BuddyHarness {
    pub fn new(heap_size: usize) -> Self {
        let region_size =
            heap_size + BuddyAllocator::<PAGE_SIZE>::required_meta_size(heap_size) + PAGE_SIZE * 4;
        let mut region = HostRegion::new(region_size);
        let mut allocator = BuddyAllocator::<PAGE_SIZE>::new();
        unsafe {
            allocator.init(region.as_mut_slice(), None).unwrap();
        }
        Self {
            _region: region,
            allocator,
        }
    }
}

pub struct SlabHarness {
    _region: HostRegion,
    buddy: BuddyAllocator<PAGE_SIZE>,
    slab: SlabAllocator<PAGE_SIZE>,
}

impl SlabHarness {
    pub fn new(heap_size: usize) -> Self {
        let region_size =
            heap_size + BuddyAllocator::<PAGE_SIZE>::required_meta_size(heap_size) + PAGE_SIZE * 4;
        let mut region = HostRegion::new(region_size);
        let mut buddy = BuddyAllocator::<PAGE_SIZE>::new();
        unsafe {
            buddy.init(region.as_mut_slice(), None).unwrap();
        }
        Self {
            _region: region,
            buddy,
            slab: SlabAllocator::new(),
        }
    }

    pub fn alloc(&mut self, layout: Layout) -> core::ptr::NonNull<u8> {
        loop {
            match self.slab.alloc(layout).unwrap() {
                SlabAllocResult::Allocated(ptr) => return ptr,
                SlabAllocResult::NeedsSlab { size_class, pages } => {
                    let slab_bytes = pages * PAGE_SIZE;
                    let base = self.buddy.alloc_pages(pages, slab_bytes).unwrap();
                    self.slab.add_slab(size_class, base, slab_bytes, 0);
                }
            }
        }
    }

    pub fn dealloc(&mut self, ptr: core::ptr::NonNull<u8>, layout: Layout) {
        match self.slab.dealloc(ptr, layout) {
            SlabDeallocResult::Done => {}
            SlabDeallocResult::FreeSlab { base, pages } => {
                self.buddy.dealloc_pages(base, pages);
            }
        }
    }
}

pub struct GlobalHarness {
    _region: HostRegion,
    pub allocator: GlobalAllocator<PAGE_SIZE>,
}

impl GlobalHarness {
    pub fn new(region_size: usize, cpu_count: usize) -> Self {
        let mut region = HostRegion::new(region_size);
        let allocator = GlobalAllocator::<PAGE_SIZE>::new();
        MOCK_OS.set_cpu(0);
        unsafe {
            allocator.init(region.as_mut_slice(), cpu_count, &MOCK_OS).unwrap();
        }
        Self {
            _region: region,
            allocator,
        }
    }
}
