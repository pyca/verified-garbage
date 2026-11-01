//! ML-DSA-87 (FIPS 204), the module-lattice-based digital signature
//! algorithm, at security category 5.
//!
//! Key generation is the verified assembly function `vg_mldsa87_keygen`
//! (contract `VG.Spec.MlDsa.keyGenContract` for `mlDsa87`),
//! `ML-DSA.KeyGen_internal` (FIPS 204 Algorithm 6); signing and verification
//! are `vg_mldsa87_sign_message` and `vg_mldsa87_verify_message`
//! (`signMessageContract` and `verifyMessageContract`), `ML-DSA.Sign` and
//! `ML-DSA.Verify` (Algorithms 2 and 3), which format the message with its
//! context string, compute the message representative `μ` and call the
//! internal algorithms on it, `vg_mldsa87_sign` and `vg_mldsa87_verify`
//! (§6), all composing the verified polynomial arithmetic and SHA-3. This
//! module supplies the randomness and working space, and destroys the
//! intermediate values (§3.6.3).
//!
//! On x86-64 and AArch64, verification is `vg_mldsa87_verify_message_cached`
//! (`verifyMessageCachedContract`), which takes the hash `tr = H(pk, 64)`
//! of the public key (FIPS 204 Algorithm 8) rather than computing it each
//! time: a [`VerifyingKey87`] keeps it, computed when the key is made from
//! its bytes or taken from the private key, which holds it.
//!
//! A private key is kept as the 32-byte seed `ξ` it is generated from
//! (§3.6.3), which [`SigningKey87::from_seed`] expands; the caller generates
//! the seed with an approved RBG. The expanded private key is never
//! exposed. HashML-DSA (§5.4) is not provided.
//!
//! Precomputed 64-byte message representatives are supported by
//! [`SigningKey87::sign_mu`] and [`VerifyingKey87::verify_mu`]. The caller
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
    name: "ML-DSA-87",
    signing_key: SigningKey87,
    verifying_key: VerifyingKey87,
    prepare_verify: crate::arch::mldsa87::vg_mldsa87_prepare_verifying_key,
    prepare_sign: crate::arch::mldsa87::vg_mldsa87_prepare_signing_key,
    sign_prepared: crate::arch::mldsa87::vg_mldsa87_sign_prepared,
    verify_prepared: crate::arch::mldsa87::vg_mldsa87_verify_prepared,
    sign_message_prepared: crate::arch::mldsa87::vg_mldsa87_sign_message_prepared,
    verify_message_prepared: crate::arch::mldsa87::vg_mldsa87_verify_message_prepared,
    sign_prepared_sha3: (crate::arch::mldsa87::vg_mldsa87_sign_prepared_sha3, crate::arch::mldsa87::VG_MLDSA87_SIGN_PREPARED_SHA3_FEATURES),
    verify_prepared_sha3: (crate::arch::mldsa87::vg_mldsa87_verify_prepared_sha3, crate::arch::mldsa87::VG_MLDSA87_VERIFY_PREPARED_SHA3_FEATURES),
    sign_message_prepared_sha3: (crate::arch::mldsa87::vg_mldsa87_sign_message_prepared_sha3, crate::arch::mldsa87::VG_MLDSA87_SIGN_MESSAGE_PREPARED_SHA3_FEATURES),
    verify_message_prepared_sha3: (crate::arch::mldsa87::vg_mldsa87_verify_message_prepared_sha3, crate::arch::mldsa87::VG_MLDSA87_VERIFY_MESSAGE_PREPARED_SHA3_FEATURES),
    keygen: crate::arch::mldsa87::vg_mldsa87_keygen,
    sign: crate::arch::mldsa87::vg_mldsa87_sign,
    verify: crate::arch::mldsa87::vg_mldsa87_verify,
    sign_message: crate::arch::mldsa87::vg_mldsa87_sign_message,
    verify_message: crate::arch::mldsa87::vg_mldsa87_verify_message,
    verify_message_cached: crate::arch::mldsa87::vg_mldsa87_verify_message_cached,
    keygen_sha3: (crate::arch::mldsa87::vg_mldsa87_keygen_sha3, crate::arch::mldsa87::VG_MLDSA87_KEYGEN_SHA3_FEATURES),
    sign_sha3: (crate::arch::mldsa87::vg_mldsa87_sign_sha3, crate::arch::mldsa87::VG_MLDSA87_SIGN_SHA3_FEATURES),
    verify_sha3: (crate::arch::mldsa87::vg_mldsa87_verify_sha3, crate::arch::mldsa87::VG_MLDSA87_VERIFY_SHA3_FEATURES),
    sign_message_sha3: (crate::arch::mldsa87::vg_mldsa87_sign_message_sha3, crate::arch::mldsa87::VG_MLDSA87_SIGN_MESSAGE_SHA3_FEATURES),
    verify_message_cached_sha3: (crate::arch::mldsa87::vg_mldsa87_verify_message_cached_sha3, crate::arch::mldsa87::VG_MLDSA87_VERIFY_MESSAGE_CACHED_SHA3_FEATURES),
    keygen_avx2: (crate::arch::mldsa87::vg_mldsa87_keygen_avx2, crate::arch::mldsa87::VG_MLDSA87_KEYGEN_AVX2_FEATURES),
    sign_avx2: (crate::arch::mldsa87::vg_mldsa87_sign_avx2, crate::arch::mldsa87::VG_MLDSA87_SIGN_AVX2_FEATURES),
    verify_avx2: (crate::arch::mldsa87::vg_mldsa87_verify_avx2, crate::arch::mldsa87::VG_MLDSA87_VERIFY_AVX2_FEATURES),
    sign_message_avx2: (crate::arch::mldsa87::vg_mldsa87_sign_message_avx2, crate::arch::mldsa87::VG_MLDSA87_SIGN_MESSAGE_AVX2_FEATURES),
    verify_message_cached_avx2: (crate::arch::mldsa87::vg_mldsa87_verify_message_cached_avx2, crate::arch::mldsa87::VG_MLDSA87_VERIFY_MESSAGE_CACHED_AVX2_FEATURES),
    k: 8,
    l: 7,
    pk: 2592,
    sk: 4896,
    sig: 4627,
    scratch: 18048,
    message_scratch: 18176,
}
