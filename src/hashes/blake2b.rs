//! BLAKE2b (RFC 7693): digests of 1 to 64 bytes, unkeyed or keyed with up to 64
//! bytes.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::blake2b::{
    vg_blake2b_finalize_auto, vg_blake2b_init_auto, vg_blake2b_update_auto,
};

super::blake2::blake2!(
    /// An incremental BLAKE2b computation of an `N`-byte digest.
    Blake2b {
        state: 192,
        block: 128,
        max: 64,
        init: vg_blake2b_init_auto,
        update: vg_blake2b_update_auto,
        finalize: vg_blake2b_finalize_auto,
    }
);

/// BLAKE2b with 64-byte digests.
pub type Blake2b512 = Blake2b<64>;
