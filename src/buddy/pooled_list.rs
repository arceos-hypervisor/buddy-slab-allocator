//! Pooled linked list implementation using global node pool
//!
//! Provides linked lists that draw nodes from a shared global pool,
//! allowing efficient use of memory across all zones and orders.

#[cfg(feature = "log")]
use log::{error, warn};

use super::{buddy_block::BuddyBlock, global_node_pool::GlobalNodePool};

/// Pooled linked list - uses nodes from global pool
///
/// This maintains only the list structure (head/tail/len), while
/// all nodes are allocated from the global pool.
pub struct PooledLinkedList {
    head: Option<usize>,
    tail: Option<usize>,
    len: usize,
}

impl PooledLinkedList {
    /// Create a new empty pooled linked list
    pub const fn new() -> Self {
        Self {
            head: None,
            tail: None,
            len: 0,
        }
    }

    /// Insert element in sorted order (ascending by address)
    /// This is used for buddy free lists to enable efficient contiguity checking
    pub fn insert_sorted(&mut self, pool: &mut GlobalNodePool, data: BuddyBlock) -> bool {
        let new_node_idx = match pool.alloc_node() {
            Some(idx) => idx,
            None => {
                error!("Global node pool exhausted");
                return false;
            }
        };

        // Find insertion position
        let mut prev_idx = None;
        let mut current_idx = self.head;
        let mut visited = 0;

        while let Some(idx) = current_idx {
            if visited > self.len {
                error!("Potential cycle detected during insert");
                // Deallocate the node
                pool.dealloc_node(new_node_idx);
                return false;
            }

            if let Some(node) = pool.get_node(idx) {
                if node.data.addr == data.addr {
                    // Block already in free list - this is a success (no-op)
                    // The caller tried to free something that's already free
                    pool.dealloc_node(new_node_idx);
                    return true;
                }
                if node.data.addr > data.addr {
                    break; // Found position
                }
                prev_idx = current_idx;
                current_idx = node.next;
            } else {
                error!("Invalid node reference in list");
                pool.dealloc_node(new_node_idx);
                return false;
            }
            visited += 1;
        }

        // Initialize the new node
        if let Some(node) = pool.get_node_mut(new_node_idx) {
            node.data = data;
            node.next = current_idx;
        } else {
            error!("Failed to get mutable reference to newly allocated node");
            pool.dealloc_node(new_node_idx);
            return false;
        }

        // Update links
        if let Some(prev) = prev_idx {
            if let Some(prev_node) = pool.get_node_mut(prev) {
                prev_node.next = Some(new_node_idx);
            }
        } else {
            self.head = Some(new_node_idx);
        }

        // Update tail if needed
        if current_idx.is_none() {
            self.tail = Some(new_node_idx);
        }

        self.len += 1;
        true
    }

    /// Check if any block in the list falls within the given address range [start, end)
    pub fn has_block_in_range(&self, pool: &GlobalNodePool, start: usize, end: usize) -> bool {
        let mut current_idx = self.head;
        let mut visited = 0;

        while let Some(idx) = current_idx {
            if visited > self.len {
                break;
            }
            if let Some(node) = pool.get_node(idx) {
                // Early termination: list is sorted by address
                if node.data.addr >= end {
                    break;
                }
                // Check if block starts within the range
                // For i < initial_order, any block in the range is a conflict.
                // Since blocks are aligned to their size, a block starting before 'start'
                // cannot overlap with [start, end) if its size is smaller than start's alignment.
                if node.data.addr >= start {
                    return true;
                }
                current_idx = node.next;
            } else {
                break;
            }
            visited += 1;
        }
        false
    }

    /// Pop an element from the front of the list
    pub fn pop_front(&mut self, pool: &mut GlobalNodePool) -> Option<BuddyBlock> {
        if self.head.is_none() {
            return None;
        }

        let head_idx = self.head?;

        if let Some(head_node) = pool.get_node_mut(head_idx) {
            self.head = head_node.next;
            if self.head.is_none() {
                self.tail = None;
            }

            let data = head_node.data;

            // Return node to pool
            pool.dealloc_node(head_idx);
            self.len -= 1;

            Some(data)
        } else {
            error!("Head node {} is corrupted", head_idx);
            None
        }
    }

    /// Check if the list is empty
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Get the length of the list
    pub fn len(&self) -> usize {
        self.len
    }

    /// Find a node by address (for buddy system)
    ///
    /// Returns (node_idx, prev_idx) where prev_idx is the node before it (or None if head)
    pub fn find_by_addr(
        &self,
        pool: &GlobalNodePool,
        addr: usize,
    ) -> Option<(usize, Option<usize>)> {
        let mut prev_idx = None;
        let mut current_idx = self.head;
        let mut visited = 0;

        while let Some(idx) = current_idx {
            if visited > self.len {
                error!("Potential cycle detected during search");
                return None;
            }

            if let Some(node) = pool.get_node(idx) {
                // Early termination: list is sorted by address
                if node.data.addr > addr {
                    break;
                }
                if node.data.addr == addr {
                    return Some((idx, prev_idx));
                }
                prev_idx = current_idx;
                current_idx = node.next;
            } else {
                break;
            }
            visited += 1;
        }

        None
    }

    /// Remove a node at the given index
    pub fn remove(&mut self, pool: &mut GlobalNodePool, node_idx: usize) -> bool {
        // Find the node
        let mut prev_idx = None;
        let mut current_idx = self.head;
        let mut visited = 0;

        while let Some(idx) = current_idx {
            if visited > self.len {
                warn!("Potential cycle detected during remove");
                return false;
            }

            if idx == node_idx {
                break;
            }
            prev_idx = current_idx;
            if let Some(node) = pool.get_node(idx) {
                current_idx = node.next;
            } else {
                break;
            }
            visited += 1;
        }

        if current_idx != Some(node_idx) {
            return false;
        }

        self.remove_with_prev_impl(pool, node_idx, prev_idx)
    }

    /// Remove a node using known prev_idx (O(1) operation)
    ///
    /// This is used when we already know the previous node index from find_by_addr(),
    /// avoiding a second traversal of the list.
    pub fn remove_with_prev(
        &mut self,
        pool: &mut GlobalNodePool,
        node_idx: usize,
        prev_idx: Option<usize>,
    ) -> bool {
        // Verify the node exists
        if pool.get_node(node_idx).is_none() {
            warn!("Invalid node index {} for remove_with_prev", node_idx);
            return false;
        }

        // Verify prev_idx leads to node_idx if provided
        if let Some(prev) = prev_idx {
            if let Some(prev_node) = pool.get_node(prev) {
                if prev_node.next != Some(node_idx) {
                    warn!("prev_idx {} does not point to node_idx {}", prev, node_idx);
                    return false;
                }
            } else {
                warn!("Invalid prev_idx {}", prev);
                return false;
            }
        } else if self.head != Some(node_idx) {
            // prev_idx is None means node should be head
            warn!("prev_idx is None but node_idx {} is not head", node_idx);
            return false;
        }

        self.remove_with_prev_impl(pool, node_idx, prev_idx)
    }

    /// Internal implementation of remove with known prev_idx
    fn remove_with_prev_impl(
        &mut self,
        pool: &mut GlobalNodePool,
        node_idx: usize,
        prev_idx: Option<usize>,
    ) -> bool {
        // Get the node's next pointer before deallocating
        let next_idx = pool.get_node(node_idx).and_then(|n| n.next);

        // Update links
        if let Some(prev) = prev_idx {
            if let Some(prev_node) = pool.get_node_mut(prev) {
                prev_node.next = next_idx;
            }
        } else {
            self.head = next_idx;
        }

        // Update tail if needed
        if self.tail == Some(node_idx) {
            if next_idx.is_none() {
                self.tail = prev_idx;
            }
        } else if self.head.is_none() {
            self.tail = None;
        }

        // Return node to pool
        pool.dealloc_node(node_idx);
        self.len -= 1;
        true
    }

    /// Get iterator over elements
    pub fn iter<'a>(&'a self, pool: &'a GlobalNodePool) -> PooledListIter<'a> {
        PooledListIter {
            pool,
            current: self.head,
        }
    }

    /// Clear all nodes from the list
    ///
    /// Returns all nodes to the global pool
    pub fn clear(&mut self, pool: &mut GlobalNodePool) {
        while let Some(_) = self.pop_front(pool) {
            // Just pop all elements
        }
    }
}

impl Default for PooledLinkedList {
    fn default() -> Self {
        Self::new()
    }
}

/// Iterator for PooledLinkedList
pub struct PooledListIter<'a> {
    pool: &'a GlobalNodePool,
    current: Option<usize>,
}

impl<'a> Iterator for PooledListIter<'a> {
    type Item = &'a BuddyBlock;

    fn next(&mut self) -> Option<Self::Item> {
        self.current.and_then(|idx| {
            if let Some(node) = self.pool.get_node(idx) {
                self.current = node.next;
                Some(&node.data)
            } else {
                self.current = None;
                None
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::buddy::ListNode;

    const TEST_NODE_COUNT: usize = 512;

    #[test]
    fn test_pooled_list_basic() {
        let mut pool: GlobalNodePool = GlobalNodePool::new();
        let mut backing = [ListNode {
            data: BuddyBlock { order: 0, addr: 0 },
            next: None,
        }; TEST_NODE_COUNT];

        let region_start = backing.as_mut_ptr() as usize;
        let region_size = core::mem::size_of_val(&backing);
        pool.init(region_start, region_size);

        let mut list: PooledLinkedList = PooledLinkedList::new();

        assert!(list.is_empty());
        assert_eq!(list.len(), 0);
        assert_eq!(pool.free_node_count(), TEST_NODE_COUNT);

        list.insert_sorted(
            &mut pool,
            BuddyBlock {
                order: 0,
                addr: 0x1000,
            },
        );
        list.insert_sorted(
            &mut pool,
            BuddyBlock {
                order: 0,
                addr: 0x2000,
            },
        );
        list.insert_sorted(
            &mut pool,
            BuddyBlock {
                order: 0,
                addr: 0x3000,
            },
        );

        assert_eq!(list.len(), 3);
        assert_eq!(pool.free_node_count(), TEST_NODE_COUNT - 3);

        assert_eq!(
            list.pop_front(&mut pool),
            Some(BuddyBlock {
                order: 0,
                addr: 0x1000
            })
        );
        assert_eq!(
            list.pop_front(&mut pool),
            Some(BuddyBlock {
                order: 0,
                addr: 0x2000
            })
        );
        assert_eq!(list.len(), 1);
        assert_eq!(pool.free_node_count(), TEST_NODE_COUNT - 1);

        // Clear remaining
        list.clear(&mut pool);
        assert!(list.is_empty());
        assert_eq!(pool.free_node_count(), TEST_NODE_COUNT);
    }

    #[test]
    fn test_insert_sorted() {
        let mut pool: GlobalNodePool = GlobalNodePool::new();
        let mut backing = [ListNode {
            data: BuddyBlock { order: 0, addr: 0 },
            next: None,
        }; TEST_NODE_COUNT];

        let region_start = backing.as_mut_ptr() as usize;
        let region_size = core::mem::size_of_val(&backing);
        pool.init(region_start, region_size);

        let mut list: PooledLinkedList = PooledLinkedList::new();

        list.insert_sorted(
            &mut pool,
            BuddyBlock {
                order: 0,
                addr: 0x5000,
            },
        );
        list.insert_sorted(
            &mut pool,
            BuddyBlock {
                order: 0,
                addr: 0x3000,
            },
        );
        list.insert_sorted(
            &mut pool,
            BuddyBlock {
                order: 0,
                addr: 0x7000,
            },
        );
        list.insert_sorted(
            &mut pool,
            BuddyBlock {
                order: 0,
                addr: 0x1000,
            },
        );

        let items: alloc::vec::Vec<_> = list.iter(&pool).collect();
        assert_eq!(items.len(), 4);
        assert_eq!(items[0].addr, 0x1000);
        assert_eq!(items[1].addr, 0x3000);
        assert_eq!(items[2].addr, 0x5000);
        assert_eq!(items[3].addr, 0x7000);
    }

    #[test]
    fn test_find_and_remove() {
        let mut pool: GlobalNodePool = GlobalNodePool::new();
        let mut backing = [ListNode {
            data: BuddyBlock { order: 0, addr: 0 },
            next: None,
        }; TEST_NODE_COUNT];

        let region_start = backing.as_mut_ptr() as usize;
        let region_size = core::mem::size_of_val(&backing);
        pool.init(region_start, region_size);

        let mut list: PooledLinkedList = PooledLinkedList::new();

        list.insert_sorted(
            &mut pool,
            BuddyBlock {
                order: 0,
                addr: 0x1000,
            },
        );
        list.insert_sorted(
            &mut pool,
            BuddyBlock {
                order: 0,
                addr: 0x2000,
            },
        );
        list.insert_sorted(
            &mut pool,
            BuddyBlock {
                order: 0,
                addr: 0x3000,
            },
        );

        let (node_idx, _) = list.find_by_addr(&pool, 0x2000).unwrap();
        assert!(list.remove(&mut pool, node_idx));

        assert_eq!(list.len(), 2);
        assert_eq!(pool.free_node_count(), TEST_NODE_COUNT - 2);

        let items: alloc::vec::Vec<_> = list.iter(&pool).collect();
        assert_eq!(items[0].addr, 0x1000);
        assert_eq!(items[1].addr, 0x3000);
    }
}
