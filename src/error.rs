/// The error type used for allocation operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocError {
    /// Invalid size, alignment, or other input parameter.
    InvalidParam,
    /// Memory added by `add_memory` overlaps with existing memory.
    MemoryOverlap,
    /// Not enough memory is available to satisfy the request.
    NoMemory,
    /// Attempted to deallocate memory that was not allocated.
    NotAllocated,
}

/// A [`Result`] alias with [`AllocError`] as the error type.
pub type AllocResult<T = ()> = Result<T, AllocError>;
