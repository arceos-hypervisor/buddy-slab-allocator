# Allocator Test Suite

本目录包含allocator模块的集成测试。单元测试位于各模块源文件中，文档测试位于公共API函数注释中。

## 测试组织结构

### 单元测试 (src/**/*.rs)
位于各模块源文件的`#[cfg(test)]`模块中，测试单个模块的功能：
- `src/buddy/buddy_allocator.rs` - Buddy分配器单元测试
- `src/buddy/global_node_pool.rs` - 全局节点池单元测试
- `src/buddy/pooled_list.rs` - 池化链表单元测试
- `src/page_allocator.rs` - 组合页分配器单元测试
- `src/slab/slab_byte_allocator.rs` - Slab字节分配器单元测试
- `src/slab/slab_cache.rs` - Slab缓存单元测试
- `src/slab/slab_node.rs` - Slab节点单元测试

### 集成测试 (tests/)
位于tests目录，测试多个模块协同工作：
- `integration_test.rs` - 完整系统集成测试

### 文档测试
位于公共API函数文档注释中的代码示例：
- `GlobalAllocator::init()` - 初始化示例
- `GlobalAllocator::alloc()` - 分配示例
- `GlobalAllocator::alloc_pages()` - 页分配示例

## 运行测试

### 运行所有测试
```bash
cd allocator
cargo test
```

### 运行单元测试
```bash
cargo test --lib
```

### 运行集成测试
```bash
cargo test --test integration_test
```

### 运行文档测试
```bash
cargo test --doc
```

### 运行特定模块的单元测试
```bash
cargo test --lib buddy_allocator
cargo test --lib slab_byte_allocator
```

### 启用统计跟踪功能
```bash
cargo test --features tracking
```

### 显示测试输出
```bash
cargo test -- --nocapture
```

### 并行运行测试
```bash
cargo test -- --test-threads=4
```

## 测试覆盖

### 功能覆盖
- ✅ 页级分配（Buddy系统）
- ✅ 字节级分配（Slab系统）
- ✅ 全局分配器协调
- ✅ 多区域支持
- ✅ 对齐要求
- ✅ 内存统计
- ✅ 错误处理
- ✅ 碎片化处理
- ✅ 合并优化

### 场景覆盖
- ✅ 基本分配/释放
- ✅ 大量小对象
- ✅ 大块内存
- ✅ 混合大小
- ✅ 交错操作
- ✅ 边界条件
- ✅ 压力测试
- ✅ 性能基准

### 错误情况覆盖
- ✅ 无效参数
- ✅ 内存不足
- ✅ 重复释放
- ✅ 对齐错误
- ✅ 超大分配

## 测试统计

- 单元测试：26个 (位于src/**/*.rs)
- 集成测试：15个 (位于tests/integration_test.rs)
- 文档测试：3个 (位于函数文档注释)

总计：44+个测试

## 持续集成

所有测试应在提交前通过：
```bash
cargo test --all-features
cargo test --no-default-features
cargo test --features tracking
```

## 性能指标

基准测试提供以下性能指标：
- 页分配吞吐量
- Slab分配延迟
- 碎片化恢复能力
- 并发分配性能
- 重新分配开销

## 注意事项

1. 所有测试使用系统分配器分配测试堆内存
2. 测试后会自动清理分配的内存
3. 某些测试可能需要较大内存（64MB）
4. 基准测试默认被忽略，需显式运行
5. 统计跟踪测试需要启用`tracking`特性

## 添加新测试

### 添加单元测试
在相应模块源文件的`#[cfg(test)]`模块中添加：
```rust
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_new_feature() {
        // 测试代码
    }
}
```

### 添加集成测试
在`tests/integration_test.rs`中添加新测试函数。

### 添加文档测试
在公共API函数文档中添加示例：
```rust
/// 函数说明
///
/// # Examples
///
/// ```no_run
/// // 示例代码
/// ```
pub fn my_function() {}
```
