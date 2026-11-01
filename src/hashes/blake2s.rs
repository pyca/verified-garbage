//! BLAKE2s (RFC 7693): digests of 1 to 32 bytes, unkeyed or keyed with up
//! to 32 bytes, over 32-bit words (see `blake2` for how the verified
//! functions are used).
//!
//! The variants of `vg_blake2s_update` and `vg_blake2s_finalize`, with the
//! same contracts, are chosen on x86-64 CPUs with the features their
//! `_FEATURES` constants name: the `_avx` ones.

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

#[cfg(test)]
mod tests {
    use super::{Blake2s, Blake2sBackend};
    use crate::cpu::detected;
    use verified_garbage_cpu::Features;

    /// The implementation chosen for each set of the features it depends on.
    #[test]
    fn select() {
        for bits in 0..(1 << crate::cpu::NAMES.len()) {
            let backend = Blake2sBackend::select(Features(bits));
            #[cfg(target_arch = "x86_64")]
            {
                let expected =
                    if Features(bits).contains(Features(verified_garbage_cpu::feature::AVX)) {
                        Blake2sBackend::Avx
                    } else {
                        Blake2sBackend::Scalar
                    };
                assert_eq!(backend, expected, "{bits:#b}");
            }
            #[cfg(not(target_arch = "x86_64"))]
            assert_eq!(backend, Blake2sBackend::Scalar);
        }
        assert_eq!(
            Blake2s::<32>::new().backend,
            Blake2sBackend::select(detected())
        );
    }
}
