//! BLAKE2s (RFC 7693): digests of 1 to 32 bytes, unkeyed or keyed with up
//! to 32 bytes, over 32-bit words (see `blake2` for how the verified
//! functions are used).
//!
//! On x86-64, CPUs with AVX run `vg_blake2s_update_avx` and
//! `vg_blake2s_finalize_avx` instead, which have the same contracts and call
//! `vg_blake2s_compress_avx`: the work vector in four 128-bit registers.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::blake2s::{
    VG_BLAKE2S_FINALIZE_AVX_FEATURES, VG_BLAKE2S_UPDATE_AVX_FEATURES, vg_blake2s_finalize_avx,
    vg_blake2s_update_avx,
};
use crate::arch::blake2s::{vg_blake2s_finalize, vg_blake2s_init, vg_blake2s_update};

pub use crate::hmac::InvalidMac;

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
    use crate::cpu::{Features, detected};

    /// The implementation chosen for each set of the features it depends on.
    #[test]
    fn select() {
        for bits in 0..(1 << crate::cpu::NAMES.len()) {
            let backend = Blake2sBackend::select(Features(bits));
            #[cfg(target_arch = "x86_64")]
            {
                let expected = if Features(bits).contains(Features::of(&["avx"])) {
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
