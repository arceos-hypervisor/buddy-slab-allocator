#![allow(dead_code)]

use buddy_slab_allocator::eii::{current_cpu_slab_impl, remote_slab_impl, virt_to_phys_impl};
use buddy_slab_allocator::{GlobalAllocator, PerCpuSlab, SlabTrait};
use core::ptr::NonNull;
use rand::{SeedableRng, rngs::StdRng};
use std::alloc::{Layout, alloc, dealloc};
use std::cell::Cell;
use std::sync::{Mutex, MutexGuard, OnceLock};

thread_local! {
    static CURRENT_CPU: Cell<usize> = const { Cell::new(0) };
}

const TEST_PAGE_SIZE: usize = 0x1000;
const MAX_TEST_CPUS: usize = 64;

fn lowmem_map(vaddr: usize) -> usize {
    vaddr & 0x0FFF_FFFF
}

pub struct GlobalTestContext {
    _guard: MutexGuard<'static, ()>,
}

fn global_test_lock() -> &'static Mutex<()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

fn test_cpu_slabs() -> &'static [PerCpuSlab<TEST_PAGE_SIZE>] {
    static SLABS: OnceLock<Box<[PerCpuSlab<TEST_PAGE_SIZE>]>> = OnceLock::new();
    SLABS.get_or_init(|| {
        (0..MAX_TEST_CPUS)
            .map(|cpu| PerCpuSlab::new(cpu as u16))
            .collect::<Vec<_>>()
            .into_boxed_slice()
    })
}

fn reset_cpu_slabs(cpu_count: usize) {
    assert!(
        cpu_count <= MAX_TEST_CPUS,
        "cpu_count exceeds test slab pool"
    );
    for slab in &test_cpu_slabs()[..cpu_count] {
        slab.reset();
    }
}

#[virt_to_phys_impl]
fn test_virt_to_phys(vaddr: usize) -> usize {
    lowmem_map(vaddr)
}

#[current_cpu_slab_impl]
fn test_current_cpu_slab() -> &'static dyn SlabTrait {
    let cpu = CURRENT_CPU.with(|slot| slot.get());
    &test_cpu_slabs()[cpu]
}

#[remote_slab_impl]
fn test_remote_slab(cpu_idx: usize) -> &'static dyn SlabTrait {
    &test_cpu_slabs()[cpu_idx]
}

pub fn set_current_cpu(cpu: usize) {
    CURRENT_CPU.with(|slot| slot.set(cpu));
}

pub fn seeded_rng(seed: u64) -> StdRng {
    StdRng::seed_from_u64(seed)
}

pub struct HostRegion {
    ptr: *mut u8,
    layout: Layout,
}

impl HostRegion {
    pub fn new(size: usize, align: usize) -> Self {
        let layout = Layout::from_size_align(size, align).unwrap();
        let ptr = unsafe { alloc(layout) };
        assert!(!ptr.is_null(), "host alloc failed");
        Self { ptr, layout }
    }

    pub fn addr(&self) -> usize {
        self.ptr as usize
    }

    pub fn len(&self) -> usize {
        self.layout.size()
    }

    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.ptr
    }

    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        unsafe { std::slice::from_raw_parts_mut(self.ptr, self.layout.size()) }
    }

    pub unsafe fn subslice(&mut self, offset: usize, len: usize) -> &mut [u8] {
        unsafe { std::slice::from_raw_parts_mut(self.ptr.add(offset), len) }
    }
}

impl Drop for HostRegion {
    fn drop(&mut self) {
        unsafe { dealloc(self.ptr, self.layout) };
    }
}

pub fn init_global_slice<const PAGE_SIZE: usize>(
    allocator: &GlobalAllocator<PAGE_SIZE>,
    region: &mut [u8],
    cpu_count: usize,
) -> GlobalTestContext {
    assert_eq!(
        PAGE_SIZE, TEST_PAGE_SIZE,
        "test EII slab pool only supports PAGE_SIZE={TEST_PAGE_SIZE:#x}"
    );
    let guard = global_test_lock().lock().unwrap();
    set_current_cpu(0);
    reset_cpu_slabs(cpu_count);
    unsafe { allocator.init(region).unwrap() };
    GlobalTestContext { _guard: guard }
}

pub fn init_global<const PAGE_SIZE: usize>(
    allocator: &GlobalAllocator<PAGE_SIZE>,
    region: &mut HostRegion,
    cpu_count: usize,
) -> GlobalTestContext {
    init_global_slice(allocator, region.as_mut_slice(), cpu_count)
}

pub fn count_free_pages<const PAGE_SIZE: usize>(allocator: &GlobalAllocator<PAGE_SIZE>) -> usize {
    let mut addrs = Vec::new();
    while let Ok(addr) = allocator.alloc_pages(1, PAGE_SIZE) {
        addrs.push(addr);
    }
    let count = addrs.len();
    for addr in addrs {
        allocator.dealloc_pages(addr, 1);
    }
    count
}

pub fn nonnull_from_addr(addr: usize) -> NonNull<u8> {
    unsafe { NonNull::new_unchecked(addr as *mut u8) }
}

pub fn virt_to_phys(vaddr: usize) -> usize {
    lowmem_map(vaddr)
}
