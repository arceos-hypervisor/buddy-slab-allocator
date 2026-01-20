//! Global node pool for buddy allocator
//!
//! Provides a single pool of list nodes shared across all zones and orders.
//! This eliminates the need for per-zone list pools and improves memory efficiency.

use super::buddy_block::BuddyBlock;

/// Simple linked list node used by the global node pool
#[derive(Debug, Clone, Copy)]
pub struct ListNode<T> {
    pub data: T,
    pub next: Option<usize>,
}

fn align_up(addr: usize, align: usize) -> usize {
    debug_assert!(align.is_power_of_two());
    (addr + align - 1) & !(align - 1)
}

/// Global node pool - all zones and orders share nodes from this pool
///
/// Nodes are carved from one or more contiguous memory regions provided
/// by the page allocator. The pool manages a single free list of nodes
/// using raw pointers (stored as usize indices).
pub struct GlobalNodePool {
    /// Free list head - points to first available node (node address)
    free_head: Option<usize>,
    /// Total number of nodes ever added to the pool
    total_nodes: usize,
    /// Current number of free nodes in the pool
    free_nodes: usize,
    /// Allocation statistics
    total_allocations: usize,
    total_deallocations: usize,
}

impl GlobalNodePool {
    /// Create a new global node pool (uninitialized, must call init())
    pub const fn new() -> Self {
        Self {
            free_head: None,
            total_nodes: 0,
            free_nodes: 0,
            total_allocations: 0,
            total_deallocations: 0,
        }
    }

    /// Initialize the global node pool with a backing memory region
    ///
    /// The region is treated as raw memory and partitioned into
    /// `ListNode<BuddyBlock>` objects, which are all added to the
    /// pool's free list.
    pub fn init(&mut self, region_start: usize, region_size: usize) {
        self.free_head = None;
        self.total_nodes = 0;
        self.free_nodes = 0;
        self.total_allocations = 0;
        self.total_deallocations = 0;
        self.add_region(region_start, region_size);
    }

    /// Add an additional memory region to the node pool
    ///
    /// This can be used to grow the pool at runtime by carving
    /// more memory from the page allocator.
    pub fn add_region(&mut self, region_start: usize, region_size: usize) {
        let node_size = core::mem::size_of::<ListNode<BuddyBlock>>();
        let align = core::mem::align_of::<ListNode<BuddyBlock>>();
        if region_size < node_size {
            return;
        }

        let mut current = align_up(region_start, align);
        let end = region_start + region_size;

        while current + node_size <= end {
            unsafe {
                let node_ptr = current as *mut ListNode<BuddyBlock>;
                core::ptr::write(
                    node_ptr,
                    ListNode {
                        data: core::mem::zeroed(),
                        next: self.free_head,
                    },
                );
            }

            self.free_head = Some(current);
            self.total_nodes += 1;
            self.free_nodes += 1;
            current += node_size;
        }
    }

    /// Allocate a node from the pool
    ///
    /// Returns the index of the allocated node, or None if pool is exhausted
    pub fn alloc_node(&mut self) -> Option<usize> {
        let node_addr = self.free_head?;

        unsafe {
            let node = &mut *(node_addr as *mut ListNode<BuddyBlock>);
            self.free_head = node.next;
            node.next = None;
        }

        self.total_allocations += 1;
        if self.free_nodes > 0 {
            self.free_nodes -= 1;
        } else {
            panic!("free_nodes: {}", self.free_nodes);
        }

        Some(node_addr)
    }

    /// Deallocate a node back to the pool
    ///
    /// The node should not be part of any active list when freed
    pub fn dealloc_node(&mut self, node_idx: usize) {
        unsafe {
            let node_ptr = node_idx as *mut ListNode<BuddyBlock>;
            core::ptr::write(
                node_ptr,
                ListNode {
                    data: core::mem::zeroed(),
                    next: self.free_head,
                },
            );
        }

        self.free_head = Some(node_idx);
        self.total_deallocations += 1;
        self.free_nodes += 1;
    }

    /// Get a reference to a node by index
    pub fn get_node(&self, node_idx: usize) -> Option<&ListNode<BuddyBlock>> {
        Some(unsafe { &*(node_idx as *const ListNode<BuddyBlock>) })
    }

    /// Get a mutable reference to a node by index
    pub fn get_node_mut(&mut self, node_idx: usize) -> Option<&mut ListNode<BuddyBlock>> {
        Some(unsafe { &mut *(node_idx as *mut ListNode<BuddyBlock>) })
    }

    /// Get the number of free nodes in the pool
    pub fn free_node_count(&self) -> usize {
        self.free_nodes
    }

    /// Get the number of allocated nodes
    pub fn allocated_node_count(&self) -> usize {
        self.total_nodes.saturating_sub(self.free_nodes)
    }

    /// Get pool statistics
    pub fn get_stats(&self) -> GlobalPoolStats {
        GlobalPoolStats {
            total_nodes: self.total_nodes,
            free_nodes: self.free_nodes,
            allocated_nodes: self.allocated_node_count(),
            total_allocations: self.total_allocations,
            total_deallocations: self.total_deallocations,
        }
    }
}

impl Default for GlobalNodePool {
    fn default() -> Self {
        Self::new()
    }
}

/// Global pool statistics
#[derive(Debug, Default, Clone)]
pub struct GlobalPoolStats {
    pub total_nodes: usize,
    pub free_nodes: usize,
    pub allocated_nodes: usize,
    pub total_allocations: usize,
    pub total_deallocations: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEST_NODE_COUNT: usize = 512;
    #[test]
    fn test_pool_init() {
        let mut pool: GlobalNodePool = GlobalNodePool::new();
        let mut backing = [ListNode {
            data: BuddyBlock { order: 0, addr: 0 },
            next: None,
        }; TEST_NODE_COUNT];

        let region_start = backing.as_mut_ptr() as usize;
        let region_size = core::mem::size_of_val(&backing);
        pool.init(region_start, region_size);

        assert_eq!(pool.free_node_count(), TEST_NODE_COUNT);
        assert_eq!(pool.allocated_node_count(), 0);
    }

    #[test]
    fn test_alloc_dealloc() {
        let mut pool: GlobalNodePool = GlobalNodePool::new();
        let mut backing = [ListNode {
            data: BuddyBlock { order: 0, addr: 0 },
            next: None,
        }; TEST_NODE_COUNT];

        let region_start = backing.as_mut_ptr() as usize;
        let region_size = core::mem::size_of_val(&backing);
        pool.init(region_start, region_size);

        let idx1 = pool.alloc_node().unwrap();
        assert_eq!(pool.free_node_count(), TEST_NODE_COUNT - 1);
        assert_eq!(pool.allocated_node_count(), 1);

        let idx2 = pool.alloc_node().unwrap();
        assert_eq!(pool.free_node_count(), TEST_NODE_COUNT - 2);

        pool.dealloc_node(idx1);
        assert_eq!(pool.free_node_count(), TEST_NODE_COUNT - 1);

        pool.dealloc_node(idx2);
        assert_eq!(pool.free_node_count(), TEST_NODE_COUNT);
    }

    #[test]
    fn test_pool_exhaustion() {
        let mut pool: GlobalNodePool = GlobalNodePool::new();
        let mut backing = [ListNode {
            data: BuddyBlock { order: 0, addr: 0 },
            next: None,
        }; TEST_NODE_COUNT];

        let region_start = backing.as_mut_ptr() as usize;
        let region_size = core::mem::size_of_val(&backing);
        pool.init(region_start, region_size);

        // Allocate all nodes
        let mut indices = alloc::vec::Vec::new();
        for _ in 0..TEST_NODE_COUNT {
            indices.push(pool.alloc_node().unwrap());
        }

        assert_eq!(pool.free_node_count(), 0);
        assert!(pool.alloc_node().is_none());

        // Free one and allocate again
        pool.dealloc_node(indices[0]);
        assert_eq!(pool.free_node_count(), 1);
        assert!(pool.alloc_node().is_some());
    }

    #[test]
    fn test_node_access() {
        let mut pool: GlobalNodePool = GlobalNodePool::new();
        let mut backing = [ListNode {
            data: BuddyBlock { order: 0, addr: 0 },
            next: None,
        }; TEST_NODE_COUNT];

        let region_start = backing.as_mut_ptr() as usize;
        let region_size = core::mem::size_of_val(&backing);
        pool.init(region_start, region_size);

        let idx = pool.alloc_node().unwrap();

        // Get mutable reference and set data
        if let Some(node) = pool.get_node_mut(idx) {
            node.data = BuddyBlock {
                order: 0,
                addr: 0x1000,
            };
        }

        // Get reference and read data
        if let Some(node) = pool.get_node(idx) {
            assert_eq!(node.data.order, 0);
            assert_eq!(node.data.addr, 0x1000);
        }
    }

    #[test]
    fn test_stats() {
        let mut pool: GlobalNodePool = GlobalNodePool::new();
        let mut backing = [ListNode {
            data: BuddyBlock { order: 0, addr: 0 },
            next: None,
        }; TEST_NODE_COUNT];

        let region_start = backing.as_mut_ptr() as usize;
        let region_size = core::mem::size_of_val(&backing);
        pool.init(region_start, region_size);

        let idx1 = pool.alloc_node().unwrap();
        let _idx2 = pool.alloc_node().unwrap();

        let stats = pool.get_stats();
        assert_eq!(stats.total_nodes, TEST_NODE_COUNT);
        assert_eq!(stats.free_nodes, TEST_NODE_COUNT - 2);
        assert_eq!(stats.allocated_nodes, 2);
        assert_eq!(stats.total_allocations, 2);
        assert_eq!(stats.total_deallocations, 0);

        pool.dealloc_node(idx1);
        let stats2 = pool.get_stats();
        assert_eq!(stats2.free_nodes, TEST_NODE_COUNT - 1);
        assert_eq!(stats2.total_deallocations, 1);
    }
}
