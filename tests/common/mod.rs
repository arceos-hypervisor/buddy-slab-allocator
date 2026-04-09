#![allow(dead_code)]

use buddy_slab_allocator::{GlobalAllocator, OsImpl};
use core::ptr::NonNull;
use rand::{SeedableRng, rngs::StdRng};
use std::alloc::{Layout, alloc, dealloc};
use std::cell::Cell;

thread_local! {
    static CURRENT_CPU: Cell<usize> = const { Cell::new(0) };
}

fn identity_map(vaddr: usize) -> usize {
    vaddr
}

fn lowmem_map(vaddr: usize) -> usize {
    vaddr & 0x0FFF_FFFF
}

pub struct ThreadAwareOs {
    mapper: fn(usize) -> usize,
}

impl ThreadAwareOs {
    pub const fn new(mapper: fn(usize) -> usize) -> Self {
        Self { mapper }
    }
}

impl OsImpl for ThreadAwareOs {
    fn current_cpu_idx(&self) -> usize {
        CURRENT_CPU.with(|cpu| cpu.get())
    }

    fn virt_to_phys(&self, vaddr: usize) -> usize {
        (self.mapper)(vaddr)
    }
}

pub static TEST_OS: ThreadAwareOs = ThreadAwareOs::new(identity_map);
pub static LOWMEM_OS: ThreadAwareOs = ThreadAwareOs::new(lowmem_map);

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
        std::slice::from_raw_parts_mut(self.ptr.add(offset), len)
    }
}

impl Drop for HostRegion {
    fn drop(&mut self) {
        unsafe { dealloc(self.ptr, self.layout) };
    }
}

pub fn init_global<const PAGE_SIZE: usize>(
    allocator: &GlobalAllocator<PAGE_SIZE>,
    region: &mut HostRegion,
    cpu_count: usize,
    os: &'static dyn OsImpl,
) {
    set_current_cpu(0);
    unsafe {
        allocator
            .init(region.as_mut_slice(), cpu_count, os)
            .unwrap()
    };
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
