//! BLAKE2b (RFC 7693): digests of 1 to 64 bytes, unkeyed or keyed with up
//! to 64 bytes, over 64-bit words (see `blake2` for how the verified
//! functions are used).
//!
//! On x86-64, CPUs with AVX2 run `vg_blake2b_update_avx2` and
//! `vg_blake2b_finalize_avx2` instead, which have the same contracts and call
//! `vg_blake2b_compress_avx2`: the work vector in four 256-bit registers.
//! CPUs with AVX-512F and AVX512VL too run the `_avx512` ones, calling
//! `vg_blake2b_compress_avx512`, which does each rotation with one `vprorq`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::blake2b::{
    VG_BLAKE2B_FINALIZE_AVX2_FEATURES, VG_BLAKE2B_FINALIZE_AVX512_FEATURES,
    VG_BLAKE2B_UPDATE_AVX2_FEATURES, VG_BLAKE2B_UPDATE_AVX512_FEATURES, vg_blake2b_finalize_avx2,
    vg_blake2b_finalize_avx512, vg_blake2b_update_avx2, vg_blake2b_update_avx512,
};
use crate::arch::blake2b::{vg_blake2b_finalize, vg_blake2b_init, vg_blake2b_update};

pub use crate::hmac::InvalidMac;

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
    use crate::cpu::{Features, detected};

    /// The implementation chosen for each set of the features it depends on.
    #[test]
    fn select() {
        for bits in 0..(1 << crate::cpu::NAMES.len()) {
            let backend = Blake2bBackend::select(Features(bits));
            #[cfg(target_arch = "x86_64")]
            {
                let f = Features(bits);
                let expected = if f.contains(Features::of(&["avx", "avx2", "avx512f", "avx512vl"]))
                {
                    Blake2bBackend::Avx512
                } else if f.contains(Features::of(&["avx", "avx2"])) {
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
