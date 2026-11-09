//! BLAKE2s (RFC 7693): digests of 1 to 32 bytes, unkeyed or keyed with up to 32
//! bytes.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::blake2s::{
    vg_blake2s_finalize_auto, vg_blake2s_init_auto, vg_blake2s_update_auto,
};

super::blake2::blake2!(
    /// An incremental BLAKE2s computation of an `N`-byte digest.
    Blake2s {
        state: 96,
        block: 64,
        max: 32,
        init: vg_blake2s_init_auto,
        update: vg_blake2s_update_auto,
        finalize: vg_blake2s_finalize_auto,
    }
);

/// BLAKE2s with 32-byte digests.
pub type Blake2s256 = Blake2s<32>;
