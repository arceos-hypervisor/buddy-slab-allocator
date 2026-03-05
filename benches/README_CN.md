# Benchmark 使用说明

本目录包含 buddy-slab-allocator 项目的性能测试和稳定性测试。

## 运行 Benchmark

```bash
cargo bench
```

### 运行特定 benchmark suite

```bash
# 测试全局分配器
cargo bench --bench global_allocator

# 测试 Buddy 页分配器
cargo bench --bench buddy_allocator

# 测试 Slab 字节分配器
cargo bench --bench slab_allocator

# 测试稳定性
cargo bench --bench stability
```

### 高级选项

```bash
# 启用 memory tracking 功能运行 benchmark
cargo bench --features tracking

# 保存基线用于后续对比
cargo bench -- --save-baseline main

# 与基线对比
cargo bench -- --baseline main

# 只运行特定 benchmark
cargo bench global_alloc_small
```

## Benchmark Suite 说明

### 1. Global Allocator Benchmarks (`global_allocator.rs`)

测试全局分配器的统一接口，自动在 Slab 和 Buddy 分配器之间路由。

**测试内容**：
- **小对象分配** (8-1024 字节)：使用 Slab 分配器
- **大对象分配** (>2048 字节)：使用 Buddy 分配器
- **分配/释放循环**：模拟真实使用场景
- **随机分配**：不同大小和模式的测试
- **混合模式**：交替进行小对象和大对象分配
- **页分配**：直接进行页级分配

**测试目标**：
- 验证自动路由机制的效率
- 评估不同大小分配的性能
- 测试实际使用场景下的表现

### 2. Buddy Allocator Benchmarks (`buddy_allocator.rs`)

专门测试 Buddy 页分配器的页级内存分配功能。

**测试内容**：
- **单页/多页分配**：不同分配大小的测试
- **带合并的释放**：自动块合并的效率
- **对齐要求**：不同对齐约束的测试
- **碎片化抗性**：长期碎片化行为测试
- **随机模式**：随机分配/释放的压力测试
- **复合分配器**：连续块组合测试
- **统计查询**：统计信息查询的性能

**测试目标**：
- 验证 Buddy 算法的性能特征
- 测试自动合并机制的有效性
- 评估碎片化程度

### 3. Slab Allocator Benchmarks (`slab_allocator.rs`)

专门测试 Slab 字节分配器的小对象分配优化。

**测试内容**：
- **大小类别**：所有支持的分配大小（8-2048 字节）
- **释放性能**：小对象的释放速度
- **对齐支持**：各种对齐要求的测试
- **随机分配**：不同大小模式的测试
- **对象池**：重用效率测试
- **混合大小**：多个大小类别的交互测试
- **压力测试**：高容量分配压力测试
- **内存压力**：接近耗尽时的行为测试

**测试目标**：
- 验证小对象分配的 O(1) 时间复杂度
- 测试不同大小类别的性能
- 评估对象池重用的效率

### 4. Stability Benchmarks (`stability.rs`)

全面的稳定性和压力测试，验证分配器在极端条件下的表现。

**测试内容**：
- **随机模式稳定性**：长期运行的随机分配/释放
- **耗尽处理**：内存限制下的优雅失败
- **碎片化抗性**：碎片化下的持续使用
- **交替模式**：特定的分配/释放序列
- **长时间运行**：扩展持续时间测试
- **快速混合大小**：不同大小的压力测试
- **页分配压力**：页级分配的压力测试
- **内存泄漏检测**：验证没有内存泄漏
- **边界情况**：最小/最大大小、奇数对齐

**测试目标**：
- 验证长时间运行的稳定性
- 检测内存泄漏
- 测试极限条件下的行为
- 确保正确处理边界情况

## Benchmark 结果解读

### 结果位置

运行 benchmark 后，Criterion 会生成详细的 HTML 格式报告：

- **位置**：`target/criterion/report/index.html`
- **内容**：性能图表、统计分析、对比基线

### 报告内容

Criterion 生成的报告包含以下信息：

- **平均时间**：执行的平均耗时
- **标准差**：性能波动程度
- **中位数**：典型性能（排除异常值）
- **最小值/最大值**：性能范围
- **样本大小**：迭代次数
- **性能图表**：随时间变化的可视化图表
- **对比分析**：与基线或之前运行的对比

### 关键性能指标

**需要关注的性能指标**：

1. **分配速度**：
   - 不同大小类别的分配时间
   - 最佳和最差情况
   - 性能一致性

2. **释放开销**：
   - 释放操作的时间
   - Buddy 系统的合并开销
   - Slab 系统的重用效率

3. **碎片化影响**：
   - 长期运行后的性能变化
   - 内存利用率
   - 大块分配成功率

4. **可扩展性**：
   - 增加负载时的性能变化
   - 并发性能（如果测试）
   - 极限容量测试

**稳定性指标**：

1. **一致性**：
   - 多次运行结果的一致性
   - 标准差大小
   - 无明显性能下降

2. **内存泄漏**：
   - 使用 `tracking` feature 验证
   - 长时间运行后内存占用稳定
   - 释放后内存完全回收

3. **错误处理**：
   - 内存耗尽时的优雅失败
   - 边界情况的正确处理
   - 无崩溃或 panic

## 自定义 Benchmark

### 修改测试参数

可以在 `benches/` 目录下的源文件中修改 benchmark 参数：

- `HEAP_SIZE`：测试堆大小（默认：16MB）
- `PAGE_SIZE`：页大小（默认：4096 字节）
- 迭代次数：根据硬件调整

### 添加新测试

1. 在对应的 benchmark 文件中添加新的测试函数
2. 使用 `criterion` 提供的宏和类型
3. 在 `criterion_group!` 中注册新测试
4. 在 `criterion_main!` 中包含新测试组

### 示例：添加新的 benchmark

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};

fn bench_my_test(c: &mut Criterion) {
    let sizes = [64, 128, 256];
    
    let mut group = c.benchmark_group("my_test");
    
    for size in sizes.iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(size), 
            size, 
            |b, _| {
                b.iter(|| {
                    // 你的测试代码
                    black_box(size)
                })
            }
        );
    }
    
    group.finish();
}

criterion_group!(benches, bench_my_test);
criterion_main!(benches);
```

## 性能优化建议

根据 benchmark 结果，可以：

1. **优化热点路径**：找到最耗时的操作进行优化
2. **减少碎片化**：调整分配策略或增加内存池
3. **改进缓存友好性**：优化数据结构和访问模式
4. **并行化**：如果合适，添加并发支持

## 常见问题

### Q: Benchmark 编译失败怎么办？

A: 最常见的原因是 Rust 版本不兼容。请确保使用 **Rust 1.93.0 或更高版本**.

如果仍然失败：
1. 清理并重新构建：`cargo clean && cargo build`
2. 检查网络连接和依赖下载
3. 更新 rustup：`rustup update`

### Q: Benchmark 运行时间太长怎么办？

A: 可以：
1. 减少迭代次数
2. 只运行特定的 benchmark
3. 调整 `HEAP_SIZE` 减小测试范围

### Q: 如何比较不同版本的性能？

A: 使用 Criterion 的基线功能：
```bash
# 第一次运行，保存基线
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
