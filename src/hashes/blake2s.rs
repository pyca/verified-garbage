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

#[cfg(target_arch = "x86_64")]
use crate::arch::blake2s::{
    VG_BLAKE2S_FINALIZE_AVX_FEATURES, VG_BLAKE2S_UPDATE_AVX_FEATURES, vg_blake2s_finalize_avx,
    vg_blake2s_update_avx,
};
use crate::arch::blake2s::{vg_blake2s_finalize, vg_blake2s_init, vg_blake2s_update};

pub use crate::invalid_mac::InvalidMac;

super::blake2::blake2!(
    /// An incremental BLAKE2s computation of an `N`-byte digest.
    Blake2s {
        state: 96,
        block: 64,
        max: 32,
        init: vg_blake2s_init,
        backends: Blake2sBackend {
            Scalar => (vg_blake2s_update, vg_blake2s_finalize),
            #[cfg(target_arch = "x86_64")]
            Avx if [VG_BLAKE2S_UPDATE_AVX_FEATURES, VG_BLAKE2S_FINALIZE_AVX_FEATURES] =>
                (vg_blake2s_update_avx, vg_blake2s_finalize_avx),
        },
    }
);

/// BLAKE2s with 32-byte digests.
pub type Blake2s256 = Blake2s<32>;
