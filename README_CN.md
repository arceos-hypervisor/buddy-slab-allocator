# buddy-slab-allocator 内存分配器

一个面向内核和嵌入式环境的 `no_std` Buddy + Slab 分配器。

## 特性

- Buddy 作为共享页分配后端
- Slab 作为小对象分配前端
- 多核 `GlobalAllocator` 门面：共享 Buddy + 每 CPU 一个 Slab
- 全局 OS provider，用于获取当前 CPU
- 可选 `tracking` 统计
- 内置 `log` 支持

## 快速开始

### 添加依赖

```toml
[dependencies]
buddy-slab-allocator = "0.1.0"
buddy-slab-allocator = { version = "0.1.0", features = ["tracking"] }
```

### 使用 `GlobalAllocator`

```rust
use buddy_slab_allocator::{GlobalAllocator, OsImpl};
use core::alloc::Layout;

const PAGE_SIZE: usize = 0x1000;

struct DemoOs;
impl OsImpl for DemoOs {
    fn current_cpu_idx(&self) -> usize {
        0
    }
    fn virt_to_phys(&self, vaddr: usize) -> usize {
        vaddr
    }
    fn phys_to_virt(&self, paddr: usize) -> usize {
        paddr
    }
}

static OS: DemoOs = DemoOs;

let allocator = GlobalAllocator::<PAGE_SIZE>::new();
let region_start = 0x8000_0000;
let region_size = 16 * 1024 * 1024;

unsafe {
    allocator
        .init(region_start, region_size, 1, &OS)
        .unwrap();
}

let layout = Layout::from_size_align(64, 8).unwrap();
let ptr = allocator.alloc(layout).unwrap();
allocator.dealloc(ptr, layout);
```

### 分别使用 Buddy 与 Slab

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

## 测试

```bash
cargo test
cargo test --features tracking
```

## Benchmark

```bash
cargo check --benches
cargo bench
cargo bench --bench buddy_allocator
cargo bench --bench slab_allocator
cargo bench --bench global_allocator
```

Benchmark 基于 `divan`，说明见 `benches/README_CN.md`。
