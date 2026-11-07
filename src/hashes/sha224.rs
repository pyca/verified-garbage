//! SHA-224 (FIPS 180-4).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::sha256::{VG_SHA224_FINALIZE_AVX2_FEATURES, VG_SHA256_UPDATE_AVX2_FEATURES};
#[cfg(target_arch = "aarch64")]
use crate::arch::sha256::{VG_SHA224_FINALIZE_SHA2_FEATURES, VG_SHA256_UPDATE_SHA2_FEATURES};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::sha256::{VG_SHA224_FINALIZE_SHANI_FEATURES, VG_SHA256_UPDATE_SHANI_FEATURES};
use crate::arch::sha256::{vg_sha224_finalize, vg_sha224_init, vg_sha256_update};
#[cfg(target_arch = "x86_64")]
use crate::arch::sha256::{vg_sha224_finalize_avx2, vg_sha256_update_avx2};
#[cfg(target_arch = "aarch64")]
use crate::arch::sha256::{vg_sha224_finalize_sha2, vg_sha256_update_sha2};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::sha256::{vg_sha224_finalize_shani, vg_sha256_update_shani};

use crate::arch::sha256::vg_sha224_digest;
#[cfg(target_arch = "x86_64")]
use crate::arch::sha256::vg_sha224_digest_avx2;
#[cfg(target_arch = "aarch64")]
use crate::arch::sha256::vg_sha224_digest_sha2;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::sha256::vg_sha224_digest_shani;

super::streaming_hash!(
    /// An incremental SHA-224 computation (FIPS 180-4 §6.3).
    Sha224 {
        state: 96,
        block: 64,
        output: 28,
        init: vg_sha224_init,
        backends: Sha224Backend {
            Scalar => (vg_sha256_update, vg_sha224_finalize),
            #[cfg(target_arch = "aarch64")]
            Sha2 if [VG_SHA256_UPDATE_SHA2_FEATURES, VG_SHA224_FINALIZE_SHA2_FEATURES] =>
                (vg_sha256_update_sha2, vg_sha224_finalize_sha2),
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            ShaNi if [VG_SHA256_UPDATE_SHANI_FEATURES, VG_SHA224_FINALIZE_SHANI_FEATURES] =>
                (vg_sha256_update_shani, vg_sha224_finalize_shani),
            #[cfg(target_arch = "x86_64")]
            Avx2 if [VG_SHA256_UPDATE_AVX2_FEATURES, VG_SHA224_FINALIZE_AVX2_FEATURES] =>
                (vg_sha256_update_avx2, vg_sha224_finalize_avx2),
        },
        digests: {
            Scalar => vg_sha224_digest,
            #[cfg(target_arch = "aarch64")]
            Sha2 => vg_sha224_digest_sha2,
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            ShaNi => vg_sha224_digest_shani,
            #[cfg(target_arch = "x86_64")]
            Avx2 => vg_sha224_digest_avx2,
        },
    }
);

#[cfg(test)]
mod tests {
    use super::Sha224;

    /// Every way of splitting a message into two updates gives the same
    /// digest, for every length around the padding boundaries.
    #[test]
    fn incremental() {
        let msg: [u8; 200] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        for len in 0..msg.len() {
            let expected = Sha224::digest(&msg[..len]);
            for split in 0..=len {
                let mut h = Sha224::default();
                h.update(&msg[..split]);
                let copy = h.clone();
                h.update(&msg[split..len]);
                assert_eq!(h.finalize(), expected);
                let mut h = copy;
                for byte in &msg[split..len] {
                    h.update(core::slice::from_ref(byte));
                }
                assert_eq!(h.finalize(), expected);
            }
        }
    }

    /// The `HashFunction` implementation is the inherent functions.
    #[test]
    fn hash_function() {
        use crate::hashes::HashFunction;
        let msg = [0x5a; 300];
        let mut h = <Sha224 as HashFunction>::new();
        HashFunction::update(&mut h, &msg[..100]);
        HashFunction::update(&mut h, &msg[100..]);
        assert_eq!(HashFunction::finalize(h), Sha224::digest(&msg));
        assert_eq!(<Sha224 as HashFunction>::digest(&msg), Sha224::digest(&msg));
        assert_eq!(
            (
                <Sha224 as HashFunction>::OUTPUT_SIZE,
                <Sha224 as HashFunction>::BLOCK_SIZE
            ),
            (28, 64)
        );
    }
}
