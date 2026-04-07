# Benchmark 使用说明

本目录包含 buddy-slab-allocator 的性能 benchmark，统一基于 `criterion`。
稳定性、耗尽恢复和长时间随机 workload 已迁移到 `tests/stress_test.rs`，不再作为 timing benchmark 运行。

## 当前 benchmark 套件

- `global_allocator.rs`
  全局分配器真实混合 workload。
- `buddy_allocator.rs`
  页分配、对齐、碎片化恢复、统计查询。
- `slab_allocator.rs`
  小对象 size class、热路径复用、steady-state 回收。

## 运行方式

```bash
# 运行全部 benchmark
cargo bench

# 运行单个 benchmark suite
cargo bench --bench buddy_allocator
cargo bench --bench slab_allocator
cargo bench --bench global_allocator

# 仅检查 benchmark 是否可编译
cargo check --benches

# 保存基线
cargo bench -- --save-baseline main

# 与基线对比
cargo bench -- --baseline main
```

## 设计原则

- 使用 `std::hint::black_box`，不再使用已废弃的 `criterion::black_box`
- 统一 `Criterion` 配置：
  - `warm_up_time = 1s`
  - `measurement_time = 5s`
  - `sample_size = 50`
- 优先 benchmark 成对的 alloc/free，避免单轮把堆推向不同状态
- 对 workload 型场景使用固定批次操作和固定随机种子
- 通过 `Throughput::{Elements, Bytes}` 明确每类 benchmark 的吞吐量口径

## 报告解读

运行 benchmark 后，Criterion 会生成 HTML 报告：

- 路径：`target/criterion/report/index.html`
- 重点关注：
  - 平均时间与置信区间
  - `Bytes/s` 或 `Elements/s` 吞吐量
  - 与 baseline 的回归或改进幅度

## 与压力测试的区别

- `benches/`
  只负责性能测量，不包含耗尽恢复、泄漏检查等强断言逻辑。
- `tests/stress_test.rs`
  负责长时间随机、碎片化恢复、耗尽恢复与 tracking 不变量检查。
cargo bench -- --save-baseline v1

# 修改代码后，对比基线
cargo bench -- --baseline v1
```

### Q: Benchmark 结果不稳定怎么办？

A: 可能原因：
1. 系统负载过高
2. 频率调整或电源管理
3. 后台程序干扰

建议：
1. 关闭不必要的程序
2. 多次运行取平均值
3. 使用固定 CPU 频率

## 参考文献

- [Criterion.rs 文档](https://bheisler.github.io/criterion.rs/book/)
- [Rust 性能优化指南](https://nnethercote.github.io/perf-book/)
- [Buddy 算法原理](https://en.wikipedia.org/wiki/Buddy_memory_allocation)
- [Slab 分配器设计](https://en.wikipedia.org/wiki/Slab_allocation)
