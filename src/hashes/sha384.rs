//! SHA-384 (FIPS 180-4).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::sha512::vg_sha384_digest;
#[cfg(target_arch = "aarch64")]
use crate::arch::sha512::vg_sha384_digest_sha3;
use crate::arch::sha512::vg_sha384_init;
#[cfg(target_arch = "x86_64")]
use crate::arch::sha512::{
    VG_SHA384_FINALIZE_AVX2_FEATURES, VG_SHA384_FINALIZE_SHANI_FEATURES,
    VG_SHA512_UPDATE_AVX2_FEATURES, VG_SHA512_UPDATE_SHANI_FEATURES,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::sha512::{VG_SHA384_FINALIZE_SHA3_FEATURES, VG_SHA512_UPDATE_SHA3_FEATURES};
#[cfg(target_arch = "x86_64")]
use crate::arch::sha512::{vg_sha384_digest_avx2, vg_sha384_digest_shani};
use crate::arch::sha512::{vg_sha384_finalize, vg_sha512_update};
#[cfg(target_arch = "x86_64")]
use crate::arch::sha512::{
    vg_sha384_finalize_avx2, vg_sha384_finalize_shani, vg_sha512_update_avx2,
    vg_sha512_update_shani,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::sha512::{vg_sha384_finalize_sha3, vg_sha512_update_sha3};

super::streaming_hash!(
    /// An incremental SHA-384 computation (FIPS 180-4 §6.5).
    Sha384 {
        state: 192,
        block: 128,
        output: 48,
        init: vg_sha384_init,
        backends: Sha384Backend {
            Scalar => (vg_sha512_update, vg_sha384_finalize),
            #[cfg(target_arch = "aarch64")]
            Sha3 if [VG_SHA512_UPDATE_SHA3_FEATURES, VG_SHA384_FINALIZE_SHA3_FEATURES] =>
                (vg_sha512_update_sha3, vg_sha384_finalize_sha3),
            #[cfg(target_arch = "x86_64")]
            ShaNi if [VG_SHA512_UPDATE_SHANI_FEATURES, VG_SHA384_FINALIZE_SHANI_FEATURES] =>
                (vg_sha512_update_shani, vg_sha384_finalize_shani),
            #[cfg(target_arch = "x86_64")]
            Avx2 if [VG_SHA512_UPDATE_AVX2_FEATURES, VG_SHA384_FINALIZE_AVX2_FEATURES] =>
                (vg_sha512_update_avx2, vg_sha384_finalize_avx2),
        },
        digests: {
            Scalar => vg_sha384_digest,
            #[cfg(target_arch = "aarch64")]
            Sha3 => vg_sha384_digest_sha3,
            #[cfg(target_arch = "x86_64")]
            ShaNi => vg_sha384_digest_shani,
            #[cfg(target_arch = "x86_64")]
            Avx2 => vg_sha384_digest_avx2,
        },
        tables: {
            Scalar => {
                hash: crate::arch::fn_tables::VG_HASH_SHA384 [],
                md_hash: crate::arch::fn_tables::VG_MD_HASH_SHA384 [],
                hmac: crate::arch::fn_tables::VG_HMAC_SHA384 [],
            },
            #[cfg(target_arch = "aarch64")]
            Sha3 => {
                hash: crate::arch::fn_tables::VG_HASH_SHA384_SHA3 [crate::arch::fn_tables::VG_HASH_SHA384_SHA3_FEATURES],
                md_hash: crate::arch::fn_tables::VG_MD_HASH_SHA384_SHA3 [crate::arch::fn_tables::VG_MD_HASH_SHA384_SHA3_FEATURES],
                hmac: crate::arch::fn_tables::VG_HMAC_SHA384_SHA3 [crate::arch::fn_tables::VG_HMAC_SHA384_SHA3_FEATURES],
            },
            #[cfg(target_arch = "x86_64")]
            ShaNi => {
                hash: crate::arch::fn_tables::VG_HASH_SHA384_SHANI [crate::arch::fn_tables::VG_HASH_SHA384_SHANI_FEATURES],
                md_hash: crate::arch::fn_tables::VG_MD_HASH_SHA384_SHANI [crate::arch::fn_tables::VG_MD_HASH_SHA384_SHANI_FEATURES],
                hmac: crate::arch::fn_tables::VG_HMAC_SHA384_SHANI [crate::arch::fn_tables::VG_HMAC_SHA384_SHANI_FEATURES],
            },
            #[cfg(target_arch = "x86_64")]
            Avx2 => {
                hash: crate::arch::fn_tables::VG_HASH_SHA384_AVX2 [crate::arch::fn_tables::VG_HASH_SHA384_AVX2_FEATURES],
                md_hash: crate::arch::fn_tables::VG_MD_HASH_SHA384_AVX2 [crate::arch::fn_tables::VG_MD_HASH_SHA384_AVX2_FEATURES],
                hmac: crate::arch::fn_tables::VG_HMAC_SHA384_AVX2 [crate::arch::fn_tables::VG_HMAC_SHA384_AVX2_FEATURES],
            },
        },
    }
);

#[cfg(test)]
mod tests {
    use super::Sha384;

    /// Every way of splitting a message into two updates gives the same
    /// digest, for every length around the padding boundaries.
    #[test]
    fn incremental() {
        let msg: [u8; 400] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        for len in 0..msg.len() {
            let expected = Sha384::digest(&msg[..len]);
            for split in 0..=len {
                let mut h = Sha384::default();
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
        let mut h = <Sha384 as HashFunction>::new();
        HashFunction::update(&mut h, &msg[..100]);
        HashFunction::update(&mut h, &msg[100..]);
        assert_eq!(HashFunction::finalize(h), Sha384::digest(&msg));
        assert_eq!(<Sha384 as HashFunction>::digest(&msg), Sha384::digest(&msg));
        assert_eq!(
            (
                <Sha384 as HashFunction>::OUTPUT_SIZE,
                <Sha384 as HashFunction>::BLOCK_SIZE
            ),
            (48, 128)
        );
    }
}
