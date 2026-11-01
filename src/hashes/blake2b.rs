//! BLAKE2b (RFC 7693): digests of 1 to 64 bytes, unkeyed or keyed with up
//! to 64 bytes, over 64-bit words (see `blake2` for how the verified
//! functions are used).
//!
//! The variants of `vg_blake2b_update` and `vg_blake2b_finalize`, with the
//! same contracts, are chosen on x86-64 CPUs with the features their
//! `_FEATURES` constants name, in this order: the `_avx512` ones, then the
//! `_avx2` ones.

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

pub use crate::invalid_mac::InvalidMac;

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

#[cfg(test)]
mod tests {
    use super::{Blake2b, Blake2bBackend};
    use crate::cpu::detected;
    use verified_garbage_cpu::Features;

    /// The implementation chosen for each set of the features it depends on.
    #[test]
    fn select() {
        for bits in 0..(1 << crate::cpu::NAMES.len()) {
            let backend = Blake2bBackend::select(Features(bits));
            #[cfg(target_arch = "x86_64")]
            {
                let f = Features(bits);
                let expected = if f.contains(Features(
                    verified_garbage_cpu::feature::AVX
                        | verified_garbage_cpu::feature::AVX2
                        | verified_garbage_cpu::feature::AVX512F
                        | verified_garbage_cpu::feature::AVX512VL,
                )) {
                    Blake2bBackend::Avx512
                } else if f.contains(Features(
                    verified_garbage_cpu::feature::AVX | verified_garbage_cpu::feature::AVX2,
                )) {
                    Blake2bBackend::Avx2
                } else {
                    Blake2bBackend::Scalar
                };
                assert_eq!(backend, expected, "{bits:#b}");
            }
            #[cfg(not(target_arch = "x86_64"))]
            assert_eq!(backend, Blake2bBackend::Scalar);
        }
        assert_eq!(
            Blake2b::<64>::new().backend,
            Blake2bBackend::select(detected())
        );
    }
}
