//! SHA-1 (FIPS 180-4).
//!
//! SHA-1 is broken as a collision-resistant hash function: use it only where an
//! existing protocol or file format requires it.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::sha1::{
    VG_SHA1_FINALIZE_AVX_BMI_FEATURES, VG_SHA1_UPDATE_AVX_BMI_FEATURES, vg_sha1_finalize_avx_bmi,
    vg_sha1_update_avx_bmi,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::sha1::{
    VG_SHA1_FINALIZE_SHA2_FEATURES, VG_SHA1_UPDATE_SHA2_FEATURES, vg_sha1_finalize_sha2,
    vg_sha1_update_sha2,
};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::sha1::{
    VG_SHA1_FINALIZE_SHANI_FEATURES, VG_SHA1_UPDATE_SHANI_FEATURES, vg_sha1_finalize_shani,
    vg_sha1_update_shani,
};
use crate::arch::sha1::{vg_sha1_finalize, vg_sha1_init, vg_sha1_update};

use crate::arch::sha1::vg_sha1_digest;
#[cfg(target_arch = "x86_64")]
use crate::arch::sha1::vg_sha1_digest_avx_bmi;
#[cfg(target_arch = "aarch64")]
use crate::arch::sha1::vg_sha1_digest_sha2;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::sha1::vg_sha1_digest_shani;

super::streaming_hash!(
    /// An incremental SHA-1 computation.
    Sha1 {
        state: 84,
        block: 64,
        output: 20,
        init: vg_sha1_init,
        backends: Sha1Backend {
            Scalar => (vg_sha1_update, vg_sha1_finalize),
            #[cfg(target_arch = "aarch64")]
            Sha2 if [VG_SHA1_UPDATE_SHA2_FEATURES, VG_SHA1_FINALIZE_SHA2_FEATURES] =>
                (vg_sha1_update_sha2, vg_sha1_finalize_sha2),
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            ShaNi if [VG_SHA1_UPDATE_SHANI_FEATURES, VG_SHA1_FINALIZE_SHANI_FEATURES] =>
                (vg_sha1_update_shani, vg_sha1_finalize_shani),
            #[cfg(target_arch = "x86_64")]
            AvxBmi if [VG_SHA1_UPDATE_AVX_BMI_FEATURES, VG_SHA1_FINALIZE_AVX_BMI_FEATURES] =>
                (vg_sha1_update_avx_bmi, vg_sha1_finalize_avx_bmi),
        },
        digests: {
            Scalar => vg_sha1_digest,
            #[cfg(target_arch = "aarch64")]
            Sha2 => vg_sha1_digest_sha2,
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            ShaNi => vg_sha1_digest_shani,
            #[cfg(target_arch = "x86_64")]
            AvxBmi => vg_sha1_digest_avx_bmi,
        },
    }
);

#[cfg(test)]
mod tests {
    use super::Sha1;

    /// Every way of splitting a message into two updates gives the same
    /// digest, for every length around the padding boundaries.
    #[test]
    fn incremental() {
        let msg: [u8; 200] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        for len in 0..msg.len() {
            let expected = Sha1::digest(&msg[..len]);
            for split in 0..=len {
                let mut h = Sha1::default();
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
        let mut h = <Sha1 as HashFunction>::new();
        HashFunction::update(&mut h, &msg[..100]);
        HashFunction::update(&mut h, &msg[100..]);
        assert_eq!(HashFunction::finalize(h), Sha1::digest(&msg));
        assert_eq!(<Sha1 as HashFunction>::digest(&msg), Sha1::digest(&msg));
        assert_eq!(<Sha1 as HashFunction>::OUTPUT_SIZE, 20);
        assert_eq!(<Sha1 as HashFunction>::BLOCK_SIZE, 64);
    }
}
