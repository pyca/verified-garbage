//! BLAKE2s (RFC 7693): digests of 1 to 32 bytes, unkeyed or keyed with up
//! to 32 bytes, over 32-bit words (see `blake2` for how the verified
//! functions are used).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm"
))]

use crate::arch::blake2s::{vg_blake2s_finalize, vg_blake2s_init, vg_blake2s_update};

/// `vg_blake2s_update`, which keeps its working space on its own stack,
/// taking the empty working space `blake2!` passes.
///
/// # Safety
///
/// As for `vg_blake2s_update`.
unsafe fn update(state: *mut [u8; 96], count: u64, data: *const u8, len: usize, _: *mut [u64; 0]) {
    // SAFETY: the caller's obligations.
    unsafe { vg_blake2s_update(state, count, data, len) }
}

/// `vg_blake2s_finalize`, which keeps its working space on its own stack,
/// taking the empty working space `blake2!` passes.
///
/// # Safety
///
/// As for `vg_blake2s_finalize`.
unsafe fn finalize(state: *mut [u8; 96], count: u64, out: *mut [u8; 32], _: *mut [u64; 0]) {
    // SAFETY: the caller's obligations.
    unsafe { vg_blake2s_finalize(state, count, out) }
}

pub use crate::hmac::InvalidMac;

super::blake2::blake2!(
    /// An incremental BLAKE2s computation of an `N`-byte digest.
    Blake2s {
        state: 96,
        scratch: 0,
        block: 64,
        max: 32,
        init: vg_blake2s_init,
        backends: Blake2sBackend {
            Scalar => (update, finalize),
        },
    }
);

/// BLAKE2s with 32-byte digests.
pub type Blake2s256 = Blake2s<32>;
