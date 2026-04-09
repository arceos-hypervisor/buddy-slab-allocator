# buddy-slab-allocator

A `no_std` buddy + slab two-level memory allocator designed for kernel and embedded environments.

## Architecture Overview

The allocator employs a classic **two-level** architecture:

1. **Buddy page allocator** — manages physical pages, the shared backend
2. **Slab byte allocator** — manages small objects (≤ 2048 bytes), the frontend
3. **GlobalAllocator** — a multi-core facade that routes allocations to per-CPU slab caches or the buddy backend

```mermaid
classDiagram
    direction TB

    class GlobalAllocator~PAGE_SIZE~ {
        -Mutex~CompositePageAllocator~ buddy
        -Option~NonNull~PerCpuSlabSlot~~ slab_slots_ptr
        -usize cpu_count
        -MetadataRegionInfo metadata_region
        -&'static dyn Os os
        -UsageStatsAtomic stats
        -AtomicBool initialized
        +new() GlobalAllocator
        +init(region, cpu_count, os) AllocResult
        +add_memory_region(start, size) AllocResult
        +alloc(Layout) Option~NonNull~u8~~
        +dealloc(ptr, Layout)
        +usage_stats() UsageStats
    }

    class Os {
        <<trait>>
        +current_cpu_idx() usize
    }

    class PerCpuSlabSlot~PAGE_SIZE~ {
        -Mutex~SlabByteAllocator~ slab
    }

    class CompositePageAllocator~PAGE_SIZE~ {
        -BuddyPageAllocator~PAGE_SIZE~ buddy
        -CompositeBlockTracker composite_tracker
        +new() CompositePageAllocator
        +init(start, size)
        +alloc_pages(count, align) AllocResult~usize~
        +dealloc_pages(addr, count)
    }

    class CompositeBlockTracker {
        -blocks: [Option~CompositeBlockInfo~; 64]
        -count: usize
    }

    class CompositeBlockInfo {
        +base_addr: usize
        +part_count: u8
        +parts: [(usize, u32); 8]
    }

    class BuddyPageAllocator~PAGE_SIZE~ {
        -zones: [BuddySet~PAGE_SIZE~; 4]
        -num_zones: usize
        -global_node_pool: GlobalNodePool
        -BuddyStats stats
        -Option~&'static dyn AddrTranslator~ addr_translator
        +alloc_pages(count, align) AllocResult~usize~
        +dealloc_pages(addr, count)
        +add_memory_region(start, size) AllocResult
    }

    class AddrTranslator {
        <<trait>>
        +virt_to_phys(va: usize) Option~usize~
    }

    class BuddySet~PAGE_SIZE~ {
        -base_addr: usize
        -end_addr: usize
        -total_pages: usize
        -zone_id: usize
        -is_lowmem: bool
        -free_lists: [PooledLinkedList; 11]
    }

    class GlobalNodePool {
        -free_head: Option~usize~
        -total_nodes: usize
        -free_nodes: usize
    }

    class PooledLinkedList {
        -head: Option~usize~
        -tail: Option~usize~
        -len: usize
        +insert_sorted(addr, order)
        +pop_front() Option~BuddyBlock~
        +find_by_addr(addr) Option~BuddyBlock~
        +remove(addr)
    }

    class BuddyBlock {
        +order: usize
        +addr: usize
    }

    class SlabByteAllocator~PAGE_SIZE~ {
        -caches: [SlabCache; 9]
        -total_bytes: usize
        -allocated_bytes: usize
        +alloc(Layout) SlabAllocDecision
        +dealloc(ptr, Layout) SlabDeallocDecision
        +provide_slab(size_class, owner_cpu, slab_base, slab_bytes)
    }

    class SizeClass {
        <<enum>>
        Bytes8 Bytes16 Bytes32 Bytes64
        Bytes128 Bytes256 Bytes512
        Bytes1024 Bytes2048
    }

    class SlabCache {
        -partial: SlabIntrusiveList
        -empty: SlabIntrusiveList
        -full: SlabIntrusiveList
        +alloc_object() Option~usize~
        +provide_slab(addr, size_class, owner_cpu, slab_bytes)
        +dealloc_object(ptr) SlabDeallocDecision
    }

    class SlabIntrusiveList {
        -head: Option~usize~
        -tail: Option~usize~
        -len: usize
    }

    class SlabNode {
        +addr: usize
        +size_class: SizeClass
        +alloc_object() Option~usize~
        +dealloc_object(ptr) bool
    }

    class SlabHeader {
        +magic: u32
        +size_class: u16
        +object_count: u16
        +free_count: u16
        +owner_cpu: u32
        +slab_bytes: usize
        +prev: usize
        +next: usize
        +free_bitmap: [u64; 8]
    }

    class AllocError {
        <<enum>>
        InvalidParam
        MemoryOverlap
        NoMemory
        NotAllocated
    }

    %% Relationships

    GlobalAllocator --> Os : uses
    GlobalAllocator *-- PerCpuSlabSlot : cpu_count slots
    GlobalAllocator *-- CompositePageAllocator : Mutex wrapped
    GlobalAllocator ..> UsageStats : returns

    CompositePageAllocator *-- BuddyPageAllocator
    CompositePageAllocator *-- CompositeBlockTracker
    CompositeBlockTracker *-- CompositeBlockInfo : tracks

    BuddyPageAllocator *-- BuddySet : up to 4 zones
    BuddyPageAllocator *-- GlobalNodePool : shared
    BuddyPageAllocator ..> AddrTranslator : optional
    BuddySet *-- PooledLinkedList : 11 free lists
    PooledLinkedList ..> GlobalNodePool : allocates nodes from
    PooledLinkedList ..> BuddyBlock : manages

    PerCpuSlabSlot *-- SlabByteAllocator : Mutex wrapped
    SlabByteAllocator *-- SlabCache : 9 size classes
    SlabByteAllocator ..> SizeClass : dispatches by
    SlabCache *-- SlabIntrusiveList : 3 lists
    SlabIntrusiveList ..> SlabNode : manages
    SlabNode *-- SlabHeader : embedded in memory
```

### Allocation Flow

```mermaid
flowchart TD
    A["GlobalAllocator::alloc(layout)"] --> B{size ≤ 2048B?}
    B -- Yes --> C["Route to per-CPU SlabByteAllocator"]
    C --> D{Slab has free object?}
    D -- Yes --> E["Return object from SlabCache"]
    D -- No --> F["Request pages from CompositePageAllocator"]
    F --> G["Provide new slab to SlabCache"]
    G --> E
    B -- No --> H["Allocate pages from CompositePageAllocator"]
    H --> I{Contiguous pages available?}
    I -- Yes --> J["Return contiguous pages"]
    I -- No --> K["Combine multiple buddy blocks (composite)"]
    K --> J
```

## Features

- **Buddy page allocator** — power-of-2 page allocation with splitting and merging
- **Slab byte allocator** — 9 fixed size classes (8B ~ 2048B) for small objects
- **Composite page allocation** — combines non-contiguous buddy blocks for large requests
- **Multi-core support** — per-CPU slab caches with `GlobalAllocator` facade
- **Multi-zone** — up to 4 memory zones with low-memory (DMA32) preference
- **Runtime memory addition** — add memory regions after initialization
- **`no_std`** — suitable for kernel and embedded environments
- **Optional `tracking`** — compile-time statistics gathering
- **Built-in `log`** — structured logging for debugging

## Quick Start

### Add Dependency

```toml
[dependencies]
buddy-slab-allocator = "0.2.0"

# With statistics tracking
buddy-slab-allocator = { version = "0.2.0", features = ["tracking"] }
```

### Using `GlobalAllocator`

The `GlobalAllocator` is the recommended interface. It automatically routes small allocations to per-CPU slab caches and large allocations to the buddy page allocator.

```rust
use buddy_slab_allocator::{GlobalAllocator, OsImpl};
use core::alloc::Layout;

const PAGE_SIZE: usize = 0x1000;

struct DemoOs;
impl OsImpl for DemoOs {
    fn current_cpu_idx(&self) -> usize { 0 }
    fn virt_to_phys(&self, vaddr: usize) -> usize { vaddr }
}

static OS: DemoOs = DemoOs;

let allocator = GlobalAllocator::<PAGE_SIZE>::new();
let region_start = 0x8000_0000 as *mut u8;
let region_size = 16 * 1024 * 1024;
let region = unsafe { core::slice::from_raw_parts_mut(region_start, region_size) };

unsafe {
    allocator.init(region, 1, &OS).unwrap();
}

let layout = Layout::from_size_align(64, 8).unwrap();
let ptr = allocator.alloc(layout).unwrap();
allocator.dealloc(ptr, layout);
```

### Using Buddy and Slab Separately

For lower-level control, use the components directly:

```rust
use buddy_slab_allocator::{
    CompositePageAllocator, SlabAllocDecision, SlabByteAllocator, SlabDeallocDecision,
};
use core::alloc::Layout;

const PAGE_SIZE: usize = 0x1000;
let mut page_alloc = CompositePageAllocator::<PAGE_SIZE>::new();
page_alloc.init(0x8000_0000, 16 * 1024 * 1024);

let mut slab_alloc = SlabByteAllocator::<PAGE_SIZE>::new();
let layout = Layout::from_size_align(64, 8).unwrap();

let ptr = loop {
    match slab_alloc.alloc(layout).unwrap() {
        SlabAllocDecision::Allocated(ptr, _) => break ptr,
        SlabAllocDecision::NeedsRefill {
            size_class,
            page_count,
            slab_bytes,
        } => {
            let slab_base = page_alloc.alloc_pages(page_count, slab_bytes).unwrap();
            slab_alloc
                .provide_slab(size_class, 0, slab_base, slab_bytes)
                .unwrap();
        }
    }
};

if let SlabDeallocDecision::ReleaseSlab {
    slab_base,
    page_count,
    ..
} = slab_alloc.dealloc(ptr, layout)
{
    page_alloc.dealloc_pages(slab_base, page_count);
}
```

## API Reference

### Core Types

- **`GlobalAllocator<PAGE_SIZE>`** — Top-level facade combining page and slab allocation
- **`CompositePageAllocator<PAGE_SIZE>`** — Page allocator with composite block support
- **`BuddyPageAllocator<PAGE_SIZE>`** — Multi-zone buddy page allocator
- **`SlabByteAllocator<PAGE_SIZE>`** — Slab allocator managing 9 size classes

### Traits

- **`Os`** — Provides CPU index for per-CPU slab routing
- **`AddrTranslator`** — Virtual-to-physical address translation for DMA32

### Allocation Decisions

The slab allocator returns decisions rather than directly allocating pages, allowing the caller to manage page allocation:

- **`SlabAllocDecision::Allocated(ptr, size)`** — object allocated successfully
- **`SlabAllocDecision::NeedsRefill { size_class, page_count, slab_bytes }`** — slab needs new pages

- **`SlabDeallocDecision::Done`** — object freed within the slab
- **`SlabDeallocDecision::ReleaseSlab { slab_base, page_count, .. }`** — slab became empty, pages can be released

## Testing & Benchmarking

```bash
# Run tests
cargo test
cargo test --features tracking

# Check benchmarks compile
cargo check --benches

# Run all benchmarks
cargo bench

# Run one benchmark suite
cargo bench --bench buddy_allocator
cargo bench --bench slab_allocator
cargo bench --bench global_allocator
```

Benchmarks are built with `divan`. Detailed benchmark notes are in `benches/README_CN.md`.

## License

Licensed under [Apache-2.0](LICENSE).
