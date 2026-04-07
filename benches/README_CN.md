# Benchmark 使用说明

本目录包含 buddy-slab-allocator 的性能 benchmark，统一基于 `criterion`。

## 当前 benchmark 套件

- `global_allocator.rs`
  多核 `GlobalAllocator` 的混合 workload
- `buddy_allocator.rs`
  Buddy 页分配、对齐、碎片化恢复、统计查询
- `slab_allocator.rs`
  Slab 前端 size class、steady-state、热路径复用

## 运行方式

```bash
# 仅检查 benchmark 是否可编译
cargo check --benches

# 运行全部 benchmark
cargo bench

# 单独运行某个 suite
cargo bench --bench buddy_allocator
cargo bench --bench slab_allocator
cargo bench --bench global_allocator
```

## 设计原则

- 使用 `std::hint::black_box`
- 统一 `criterion` 配置
- 尽量 benchmark 成对的 alloc/free
- 固定 workload 批次与随机种子
- 使用 `Throughput::{Elements, Bytes}` 表达吞吐量

## 与压力测试的区别

- `benches/`
  只做性能测量
- `tests/stress_test.rs`
  负责长时间随机、碎片化恢复、耗尽恢复与 tracking 不变量
