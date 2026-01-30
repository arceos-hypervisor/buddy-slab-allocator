# buddy-slab-allocator 内存分配器

一个高效的页级和字节级内存分配器，为嵌入式/内核环境设计。

## 特性

- **Buddy 页分配器**：页级内存分配
- **Slab 字节分配器**：小对象分配
- **复合页分配器**：统一的多区域页分配接口
- **全局分配器**：协调页分配器和字节分配器，提供统一的分配接口
- **零 `std` 依赖**：完全 `#![no_std]`，适合嵌入式和内核环境
- **条件日志**：支持 `log` feature 启用日志，默认无依赖
- **内存追踪**：支持 `tracking` feature 收集详细统计信息

## 快速开始

### 添加依赖

在 `Cargo.toml` 中添加：

```toml
[dependencies]
buddy-slab-allocator = "0.1.0"

# 可选功能
buddy-slab-allocator = { version = "0.1.0", features = ["log"] }      # 启用日志
buddy-slab-allocator = { version = "0.1.0", features = ["tracking"] }  # 启用追踪
```

### 基本使用

#### 使用全局分配器

```rust
use buddy_slab_allocator::GlobalAllocator;
use core::alloc::Layout;

// 创建全局分配器
let mut global = GlobalAllocator::new();

// 使用内存区域初始化全局分配器
let heap_start = 0x8000_0000;
let heap_size = 16 * 1024 * 1024; // 16MB
global.init(heap_start, heap_size).unwrap();

// 或添加多个内存池
global.add_memory(0x80000000, 0x1000000).unwrap();
global.add_memory(0x81000000, 0x1000000).unwrap();

// 小于 2048 byte 的小对象分配（自动使用 Slab）
let small_layout = Layout::from_size_align(64, 8).unwrap();
let small_ptr = global.alloc(small_layout).unwrap();

// 大对象分配（自动使用页分配器）
let large_layout = Layout::from_size_align(0x1000, 0x1000).unwrap();
let large_ptr = global.alloc(large_layout).unwrap();

// 释放内存
global.dealloc(small_ptr, small_layout);
global.dealloc(large_ptr, large_layout);
```

#### 直接使用页分配器

```rust
use buddy_slab_allocator::CompositePageAllocator;

const PAGE_SIZE: usize = 0x1000;
let mut page_alloc = CompositePageAllocator::<PAGE_SIZE>::new();

// 使用内存区域初始化
page_alloc.init(0x8000_0000, 16 * 1024 * 1024).unwrap();

// 分配页
let addr = page_alloc.alloc_pages(4, PAGE_SIZE).unwrap();
// 使用分配的内存...
page_alloc.dealloc_pages(addr, 4);
```

#### 直接使用 Slab 分配器

```rust
use buddy_slab_allocator::SlabByteAllocator;
use buddy_slab_allocator::page_allocator::PageAllocatorForSlab;
use buddy_slab_allocator::CompositePageAllocator;
use core::alloc::Layout;

const PAGE_SIZE: usize = 0x1000;
let mut page_alloc = CompositePageAllocator::<PAGE_SIZE>::new();
page_alloc.init(0x8000_0000, 16 * 1024 * 1024).unwrap();

let mut slab_alloc = SlabByteAllocator::<PAGE_SIZE>::new();

// 小对象分配快速
let layout = Layout::from_size_align(64, 8).unwrap();
let ptr = slab_alloc.alloc(&mut page_alloc, layout).unwrap();

// 释放内存
slab_alloc.dealloc(&mut page_alloc, ptr, layout);
```

## 特性详解

### 条件日志

通过 `log` feature 启用日志功能：

```toml
buddy-slab-allocator = { version = "0.1.0", features = ["log"] }
```

启用后可使用标准 `log` crate 的宏记录分配事件：

```rust
log::info!("分配内存于 {:x}", addr);
```

未启用时，日志调用会被编译为空操作，零运行时开销。

### 内存追踪

通过 `tracking` feature 启用详细的内存使用追踪：

```toml
buddy-slab-allocator = { version = "0.1.0", features = ["tracking"] }
```

启用后可以：
- 收集每种内存用途的字节数统计
- 记录每次分配的回溯信息
- 跟踪分配代际变化

## 性能特性

- **快速分配**：小对象分配 O(1) 时间复杂度
- **内存效率**：Buddy 算法有效减少外部碎片
- **自动合并**：释放的页面自动合并，减少碎片

## 测试

运行测试套件：

```bash
# 运行所有测试
cargo test --package buddy-slab-allocator

# 启用日志运行测试
cargo test --package buddy-slab-allocator --features log

# 启用追踪运行测试
cargo test --package buddy-slab-allocator --features tracking
```

## 文档

API 文档可在 [docs.rs](https://docs.rs/buddy-slab-allocator) 上查看。

在本地构建和查看文档：

```bash
cargo doc --no-deps --open
```

## 许可证

本项目采用以下许可证：

- **GPL-3.0-or-later** 或
- **Apache-2.0** 或
- **MIT**

你可以选择其中任何一种许可证使用。

## 贡献

欢迎贡献！请随时提交 Pull Request。

## 仓库

[https://github.com/arceos-hypervisor/buddy-slab-allocator](https://github.com/arceos-hypervisor/buddy-slab-allocator)
