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
buddy-slab-allocator = { path = "allocator" }

# 可选功能
buddy-slab-allocator = { path = "allocator", features = ["log"] }    # 启用日志
buddy-slab-allocator = { path = "allocator", features = ["tracking"] } # 启用追踪
```

### 基本使用

#### 使用全局分配器

```rust
use buddy_slab_allocator::GlobalAllocator;
use core::alloc::Layout;

// 创建全局分配器
let mut global = GlobalAllocator::new();

// 初始化全局分配器
global.init().unwrap();

// 添加内存池
global.add_memory(0x80000000, 0x1000000).unwrap(); 

// 不大于2048byte小对象分配 (自动使用 Slab)
let small_layout = Layout::from_size_align(64, 8).unwrap();
let small_ptr = global.alloc(small_layout).unwrap();

// 大对象分配 (自动使用页分配器)
let large_layout = Layout::from_size_align(0x1000, 0x1000).unwrap();
let large_ptr = global.alloc(large_layout).unwrap();

// 释放内存
global.dealloc(small_ptr, small_layout);
global.dealloc(large_ptr, large_layout);
```

## 特性详解

### 条件日志

通过 `log` feature 启用日志功能：

```toml
buddy-slab-allocator = { path = "allocator", features = ["log"] }
```

启用后可使用标准 `log` crate 的宏记录分配事件：

```rust
log::info!("分配内存于 {:x}", addr);
```

未启用时，日志调用会被编译为空操作，零运行时开销。

### 内存追踪

通过 `tracking` feature 启用详细的内存使用追踪：

```toml
buddy-slab-allocator = { path = "allocator", features = ["tracking"] }
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
```
