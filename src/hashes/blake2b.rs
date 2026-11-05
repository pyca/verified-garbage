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

#[cfg(target_arch = "x86_64")]
use crate::arch::blake2b::{
    VG_BLAKE2B_FINALIZE_AVX2_FEATURES, VG_BLAKE2B_FINALIZE_AVX512_FEATURES,
    VG_BLAKE2B_UPDATE_AVX2_FEATURES, VG_BLAKE2B_UPDATE_AVX512_FEATURES, vg_blake2b_finalize_avx2,
    vg_blake2b_finalize_avx512, vg_blake2b_update_avx2, vg_blake2b_update_avx512,
};
use crate::arch::blake2b::{vg_blake2b_finalize, vg_blake2b_init, vg_blake2b_update};

super::blake2::blake2!(
    /// An incremental BLAKE2b computation of an `N`-byte digest.
    Blake2b {
        state: 192,
        block: 128,
        max: 64,
        init: vg_blake2b_init,
        backends: Blake2bBackend {
            Scalar => (vg_blake2b_update, vg_blake2b_finalize),
            #[cfg(target_arch = "x86_64")]
            Avx512 if [VG_BLAKE2B_UPDATE_AVX512_FEATURES, VG_BLAKE2B_FINALIZE_AVX512_FEATURES] =>
                (vg_blake2b_update_avx512, vg_blake2b_finalize_avx512),
            #[cfg(target_arch = "x86_64")]
            Avx2 if [VG_BLAKE2B_UPDATE_AVX2_FEATURES, VG_BLAKE2B_FINALIZE_AVX2_FEATURES] =>
                (vg_blake2b_update_avx2, vg_blake2b_finalize_avx2),
        },
    }
);

/// BLAKE2b with 64-byte digests.
pub type Blake2b512 = Blake2b<64>;
