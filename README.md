# buddy-slab-allocator

A `no_std` buddy + slab allocator for kernel and embedded environments.

## Features

- Buddy page allocator as the shared page backend
- Slab byte allocator as the small-object frontend
- Multi-core `GlobalAllocator` facade with per-CPU slab fronts
- Global OS provider for CPU-local routing
- Optional `tracking` statistics
- Built-in `log` support

## Quick Start

### Add Dependency

```toml
[dependencies]
buddy-slab-allocator = "0.1.0"
buddy-slab-allocator = { version = "0.1.0", features = ["tracking"] }
```

### Using `GlobalAllocator`

```rust
use buddy_slab_allocator::{GlobalAllocator, Os};
use core::alloc::Layout;

const PAGE_SIZE: usize = 0x1000;

struct DemoOs;
impl Os for DemoOs {
    fn current_cpu_idx(&self) -> usize {
        0
    }
}

static OS: DemoOs = DemoOs;

let mut allocator = GlobalAllocator::<PAGE_SIZE>::new();

let meta_start = 0x8100_0000;
let meta_size = GlobalAllocator::<PAGE_SIZE>::required_metadata_size(1);
let heap_start = 0x8000_0000;
let heap_size = 16 * 1024 * 1024;

unsafe {
    allocator
        .init(meta_start, meta_size, heap_start, heap_size, 1, &OS)
        .unwrap();
}

let layout = Layout::from_size_align(64, 8).unwrap();
let ptr = allocator.alloc(layout).unwrap();
allocator.dealloc(ptr, layout);
```

### Using Buddy and Slab Separately

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

## Testing

```bash
cargo test
cargo test --features tracking
```

## Benchmarking

```bash
cargo check --benches
cargo bench
```

Detailed benchmark notes are in `benches/README_CN.md`.
