//! ML-DSA-44 (FIPS 204), the module-lattice-based digital signature
//! algorithm, at security category 2.
//!
//! Key generation is the verified assembly function `vg_mldsa44_keygen`
//! (contract `VG.Spec.MlDsa.keyGenContract` for `mlDsa44`),
//! `ML-DSA.KeyGen_internal` (FIPS 204 Algorithm 6); signing and verification
//! are `vg_mldsa44_sign_message` and `vg_mldsa44_verify_message`
//! (`signMessageContract` and `verifyMessageContract`), `ML-DSA.Sign` and
//! `ML-DSA.Verify` (Algorithms 2 and 3), which format the message with its
//! context string, compute the message representative `μ` and call the
//! internal algorithms on it, `vg_mldsa44_sign` and `vg_mldsa44_verify`
//! (§6). This module supplies the randomness and working space, and
//! destroys the intermediate values (§3.6.3).
//!
//! On x86-64 and AArch64, verification is `vg_mldsa44_verify_message_cached`
//! (`verifyMessageCachedContract`), which takes the hash `tr = H(pk, 64)`
//! of the public key (FIPS 204 Algorithm 8) rather than computing it each
//! time: a [`VerifyingKey44`] keeps it, computed when the key is made from
//! its bytes or taken from the private key, which holds it.
//!
//! Their variants, with the same contracts, are chosen with
//! `crate::mldsa_common::Backend` on CPUs with the features their
//! `_FEATURES` constants name: the `_avx2` ones on x86-64, the `_sha3` ones
//! on AArch64.
//!
//! A private key is kept as the 32-byte seed `ξ` it is generated from
//! (§3.6.3), which [`SigningKey44::from_seed`] expands; the caller generates
//! the seed with an approved RBG. The expanded private key is never
//! exposed. HashML-DSA (§5.4) is not provided.
//!
//! Precomputed 64-byte message representatives are supported by
//! [`SigningKey44::sign_mu`] and [`VerifyingKey44::verify_mu`]. The caller
//! computes `μ`, including the public-key hash and message formatting,
//! and supplies the signing randomness.
//!
//! The loops FIPS 204 lets an implementation bound (Appendix C) reach their
//! bounds with probability about 2⁻²⁵⁶ or less; the operation then fails
//! with [`Error::LoopBound`].

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]

crate::mldsa_common::ml_dsa! {
    name: "ML-DSA-44",
    signing_key: SigningKey44,
    verifying_key: VerifyingKey44,
    keygen: crate::arch::mldsa44::vg_mldsa44_keygen,
    sign: crate::arch::mldsa44::vg_mldsa44_sign,
    verify: crate::arch::mldsa44::vg_mldsa44_verify,
    sign_message: crate::arch::mldsa44::vg_mldsa44_sign_message,
    verify_message: crate::arch::mldsa44::vg_mldsa44_verify_message,
    verify_message_cached: crate::arch::mldsa44::vg_mldsa44_verify_message_cached,
    keygen_sha3: (crate::arch::mldsa44::vg_mldsa44_keygen_sha3, crate::arch::mldsa44::VG_MLDSA44_KEYGEN_SHA3_FEATURES),
    sign_sha3: (crate::arch::mldsa44::vg_mldsa44_sign_sha3, crate::arch::mldsa44::VG_MLDSA44_SIGN_SHA3_FEATURES),
    verify_sha3: (crate::arch::mldsa44::vg_mldsa44_verify_sha3, crate::arch::mldsa44::VG_MLDSA44_VERIFY_SHA3_FEATURES),
    sign_message_sha3: (crate::arch::mldsa44::vg_mldsa44_sign_message_sha3, crate::arch::mldsa44::VG_MLDSA44_SIGN_MESSAGE_SHA3_FEATURES),
    verify_message_cached_sha3: (crate::arch::mldsa44::vg_mldsa44_verify_message_cached_sha3, crate::arch::mldsa44::VG_MLDSA44_VERIFY_MESSAGE_CACHED_SHA3_FEATURES),
    keygen_avx2: (crate::arch::mldsa44::vg_mldsa44_keygen_avx2, crate::arch::mldsa44::VG_MLDSA44_KEYGEN_AVX2_FEATURES),
    sign_avx2: (crate::arch::mldsa44::vg_mldsa44_sign_avx2, crate::arch::mldsa44::VG_MLDSA44_SIGN_AVX2_FEATURES),
    verify_avx2: (crate::arch::mldsa44::vg_mldsa44_verify_avx2, crate::arch::mldsa44::VG_MLDSA44_VERIFY_AVX2_FEATURES),
    sign_message_avx2: (crate::arch::mldsa44::vg_mldsa44_sign_message_avx2, crate::arch::mldsa44::VG_MLDSA44_SIGN_MESSAGE_AVX2_FEATURES),
    verify_message_cached_avx2: (crate::arch::mldsa44::vg_mldsa44_verify_message_cached_avx2, crate::arch::mldsa44::VG_MLDSA44_VERIFY_MESSAGE_CACHED_AVX2_FEATURES),
    pk: 1312,
    sk: 2560,
    sig: 2420,
    scratch: 9728,
    message_scratch: 9856,
}
