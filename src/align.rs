//! Cache-line alignment of the memory the verified functions work in.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

/// `T` at the start of a 64-byte cache line.
///
/// The buffers the library gives the verified functions to work in (scratch
/// space, working space, states and key schedules) are arrays of `u8` or
/// `u64`, aligned to at most 8 bytes, and the implementations load and store
/// 16-, 32- and 64-byte vectors in them. At 8 bytes' alignment some of those
/// accesses would cross cache lines, depending on where the caller's stack or
/// the allocator put the buffer, which changed the functions' speed (by up
/// to a fifth) with unrelated changes to their callers.
#[derive(Clone, Copy)]
#[repr(C, align(64))]
pub(crate) struct CacheAligned<T>(pub(crate) T);
