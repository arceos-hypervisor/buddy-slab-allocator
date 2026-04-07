# buddy-slab-allocator

A high-performance page-level and byte-level memory allocator designed for embedded/kernel environments.

## Features

- **Buddy Page Allocator**: Page-level memory allocation
- **Slab Byte Allocator**: Small object allocation
- **Composite Page Allocator**: Unified multi-region page allocation interface
- **Global Allocator**: Coordinates page and byte allocators with unified allocation interface
- **Zero `std` Dependency**: Fully `#![no_std]`, suitable for embedded and kernel environments
- **Logging Support**: Built on the `log` crate and available by default
- **Memory Tracking**: Support `tracking` feature for detailed statistics

## Quick Start

### Add Dependency

Add to your `Cargo.toml`:

```toml
[dependencies]
buddy-slab-allocator = "0.1.0"
buddy-slab-allocator = { version = "0.1.0", features = ["tracking"] }  # Enable tracking
```

### Basic Usage

#### Using Global Allocator

```rust
use buddy_slab_allocator::GlobalAllocator;
use core::alloc::Layout;

// Create global allocator
let mut global = GlobalAllocator::new();

// Initialize the global allocator with memory region
let heap_start = 0x8000_0000;
let heap_size = 16 * 1024 * 1024; // 16MB
global.init(heap_start, heap_size).unwrap();

// Or add multiple memory pools
global.add_memory(0x80000000, 0x1000000).unwrap();
global.add_memory(0x81000000, 0x1000000).unwrap();

// Small object allocation (automatically uses Slab allocator)
let small_layout = Layout::from_size_align(64, 8).unwrap();
let small_ptr = global.alloc(small_layout).unwrap();

// Large object allocation (automatically uses page allocator)
let large_layout = Layout::from_size_align(0x1000, 0x1000).unwrap();
let large_ptr = global.alloc(large_layout).unwrap();

// Free memory
global.dealloc(small_ptr, small_layout);
global.dealloc(large_ptr, large_layout);
```

#### Using Page Allocator Directly

```rust
use buddy_slab_allocator::CompositePageAllocator;

const PAGE_SIZE: usize = 0x1000;
let mut page_alloc = CompositePageAllocator::<PAGE_SIZE>::new();

// Initialize with memory region
page_alloc.init(0x8000_0000, 16 * 1024 * 1024).unwrap();

// Allocate pages
let addr = page_alloc.alloc_pages(4, PAGE_SIZE).unwrap();
// Use the allocated memory...
page_alloc.dealloc_pages(addr, 4);
```

#### Using Slab Allocator Directly

```rust
use buddy_slab_allocator::SlabByteAllocator;
use buddy_slab_allocator::{CompositePageAllocator, PageAllocatorForSlab};
use core::alloc::Layout;

const PAGE_SIZE: usize = 0x1000;
let mut page_alloc = CompositePageAllocator::<PAGE_SIZE>::new();
page_alloc.init(0x8000_0000, 16 * 1024 * 1024).unwrap();

let mut slab_alloc = SlabByteAllocator::<PAGE_SIZE>::new();
slab_alloc.set_page_allocator(&mut page_alloc as *mut _ as *mut dyn PageAllocatorForSlab);

// Small allocations are fast
let layout = Layout::from_size_align(64, 8).unwrap();
let ptr = slab_alloc.alloc(layout).unwrap();

// Free memory
slab_alloc.dealloc(ptr, layout);
```

## Features Details

### Logging

```toml
buddy-slab-allocator = "0.1.0"
```

You can use standard `log` crate macros to log allocation events:

```rust
log::info!("Allocated memory at {:x}", addr);
```

### Memory Tracking

Enable detailed memory usage tracking via `tracking` feature:

```toml
buddy-slab-allocator = { version = "0.1.0", features = ["tracking"] }
```

After enabling, you can:
- Collect statistics of bytes allocated for each memory usage
- Record backtrace information for each allocation
- Track allocation generation changes

## Performance

- **Fast Allocation**: Small object allocation has O(1) time complexity
- **Memory Efficiency**: Buddy algorithm effectively reduces external fragmentation
- **Auto Merge**: Freed pages automatically merge to reduce fragmentation

## Testing

Run the test suite:

```bash
# Run all tests
cargo test --package buddy-slab-allocator

# Run tests with tracking enabled
cargo test --package buddy-slab-allocator --features tracking
```

## Benchmarking

This project includes comprehensive benchmarks to evaluate performance and stability under various conditions. For detailed instructions, see `benches/README.md`.

```bash
# Run all benchmarks
cargo bench
```

For detailed usage instructions, refer to `benches/README.md`.

## Documentation

API documentation is available on [docs.rs](https://docs.rs/buddy-slab-allocator).

To build and view documentation locally:

```bash
cargo doc --no-deps --open
```

## License

This project is licensed under:

- **GPL-3.0-or-later** OR
- **Apache-2.0** OR
- **MIT**

You may choose any of these licenses for your use.

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request.

## Repository

[https://github.com/arceos-hypervisor/buddy-slab-allocator](https://github.com/arceos-hypervisor/buddy-slab-allocator)

## Chinese Documentation

中文文档请查看 [README_CN.md](README_CN.md)
