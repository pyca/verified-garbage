//! ML-DSA-44 (FIPS 204), the module-lattice-based digital signature algorithm,
//! at security category 2.
//!
//! A private key is the 32-byte seed `ξ` it is generated from
//! ([`SigningKey44::from_seed`]), which the caller generates with an approved
//! RBG; the expanded private key is never exposed. HashML-DSA (§5.4) is not
//! provided. [`SigningKey44::sign_mu`] and [`VerifyingKey44::verify_mu`] take a
//! message representative `μ` that the caller computes (formatting the message
//! and hashing the public key), and the caller supplies the signing randomness.
//! A key that signs or verifies many messages can be prepared for them
//! ([`SigningKey44::prepare`], [`VerifyingKey44::prepare`]), which may make
//! each signature or verification faster.
//! Key generation's and signing's timing may depend on values that SHAKE
//! derives from secrets (see the README's "What the constant-time guarantee
//! assumes"). An operation fails with [`MlDsaError::LoopBound`] if it reaches
//! one of the loop bounds of Appendix C, with probability about 2⁻²⁵⁶ or less.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
))]

crate::mldsa_common::ml_dsa! {
    name: "ML-DSA-44",
    signing_key: SigningKey44,
    verifying_key: VerifyingKey44,
    prepared_signing_key: PreparedSigningKey44,
    prepared_verifying_key: PreparedVerifyingKey44,
    keygen: crate::arch::mldsa44::vg_mldsa44_keygen,
    sign: crate::arch::mldsa44::vg_mldsa44_sign,
    verify: crate::arch::mldsa44::vg_mldsa44_verify,
    sign_message: crate::arch::mldsa44::vg_mldsa44_sign_message,
    verify_message_cached: crate::arch::mldsa44::vg_mldsa44_verify_message_cached,
    pk_tr: crate::arch::mldsa44::vg_mldsa44_pk_tr,
    prepare_sign: crate::arch::mldsa44::vg_mldsa44_prepare_signing_key,
    prepare_verify: crate::arch::mldsa44::vg_mldsa44_prepare_verifying_key,
    sign_message_prepared: crate::arch::mldsa44::vg_mldsa44_sign_message_prepared,
    verify_message_prepared: crate::arch::mldsa44::vg_mldsa44_verify_message_prepared,
    keygen_sha3: (crate::arch::mldsa44::vg_mldsa44_keygen_sha3, crate::arch::mldsa44::VG_MLDSA44_KEYGEN_SHA3_FEATURES),
    sign_sha3: (crate::arch::mldsa44::vg_mldsa44_sign_sha3, crate::arch::mldsa44::VG_MLDSA44_SIGN_SHA3_FEATURES),
    verify_sha3: (crate::arch::mldsa44::vg_mldsa44_verify_sha3, crate::arch::mldsa44::VG_MLDSA44_VERIFY_SHA3_FEATURES),
    sign_message_sha3: (crate::arch::mldsa44::vg_mldsa44_sign_message_sha3, crate::arch::mldsa44::VG_MLDSA44_SIGN_MESSAGE_SHA3_FEATURES),
    verify_message_cached_sha3: (crate::arch::mldsa44::vg_mldsa44_verify_message_cached_sha3, crate::arch::mldsa44::VG_MLDSA44_VERIFY_MESSAGE_CACHED_SHA3_FEATURES),
    pk_tr_sha3: (crate::arch::mldsa44::vg_mldsa44_pk_tr_sha3, crate::arch::mldsa44::VG_MLDSA44_PK_TR_SHA3_FEATURES),
    sign_message_prepared_sha3: (crate::arch::mldsa44::vg_mldsa44_sign_message_prepared_sha3, crate::arch::mldsa44::VG_MLDSA44_SIGN_MESSAGE_PREPARED_SHA3_FEATURES),
    verify_message_prepared_sha3: (crate::arch::mldsa44::vg_mldsa44_verify_message_prepared_sha3, crate::arch::mldsa44::VG_MLDSA44_VERIFY_MESSAGE_PREPARED_SHA3_FEATURES),
    keygen_avx2: (crate::arch::mldsa44::vg_mldsa44_keygen_avx2, crate::arch::mldsa44::VG_MLDSA44_KEYGEN_AVX2_FEATURES),
    keygen_avx512: (crate::arch::mldsa44::vg_mldsa44_keygen_avx512, crate::arch::mldsa44::VG_MLDSA44_KEYGEN_AVX512_FEATURES),
    sign_avx2: (crate::arch::mldsa44::vg_mldsa44_sign_avx2, crate::arch::mldsa44::VG_MLDSA44_SIGN_AVX2_FEATURES),
    sign_avx512: (crate::arch::mldsa44::vg_mldsa44_sign_avx512, crate::arch::mldsa44::VG_MLDSA44_SIGN_AVX512_FEATURES),
    verify_avx2: (crate::arch::mldsa44::vg_mldsa44_verify_avx2, crate::arch::mldsa44::VG_MLDSA44_VERIFY_AVX2_FEATURES),
    verify_avx512: (crate::arch::mldsa44::vg_mldsa44_verify_avx512, crate::arch::mldsa44::VG_MLDSA44_VERIFY_AVX512_FEATURES),
    sign_message_avx2: (crate::arch::mldsa44::vg_mldsa44_sign_message_avx2, crate::arch::mldsa44::VG_MLDSA44_SIGN_MESSAGE_AVX2_FEATURES),
    sign_message_avx512: (crate::arch::mldsa44::vg_mldsa44_sign_message_avx512, crate::arch::mldsa44::VG_MLDSA44_SIGN_MESSAGE_AVX512_FEATURES),
    verify_message_cached_avx2: (crate::arch::mldsa44::vg_mldsa44_verify_message_cached_avx2, crate::arch::mldsa44::VG_MLDSA44_VERIFY_MESSAGE_CACHED_AVX2_FEATURES),
    verify_message_cached_avx512: (crate::arch::mldsa44::vg_mldsa44_verify_message_cached_avx512, crate::arch::mldsa44::VG_MLDSA44_VERIFY_MESSAGE_CACHED_AVX512_FEATURES),
    prepare_sign_avx2: (crate::arch::mldsa44::vg_mldsa44_prepare_signing_key_avx2, crate::arch::mldsa44::VG_MLDSA44_PREPARE_SIGNING_KEY_AVX2_FEATURES),
    prepare_sign_avx512: (crate::arch::mldsa44::vg_mldsa44_prepare_signing_key_avx512, crate::arch::mldsa44::VG_MLDSA44_PREPARE_SIGNING_KEY_AVX512_FEATURES),
    prepare_verify_avx2: (crate::arch::mldsa44::vg_mldsa44_prepare_verifying_key_avx2, crate::arch::mldsa44::VG_MLDSA44_PREPARE_VERIFYING_KEY_AVX2_FEATURES),
    prepare_verify_avx512: (crate::arch::mldsa44::vg_mldsa44_prepare_verifying_key_avx512, crate::arch::mldsa44::VG_MLDSA44_PREPARE_VERIFYING_KEY_AVX512_FEATURES),
    sign_message_prepared_avx2: (crate::arch::mldsa44::vg_mldsa44_sign_message_prepared_avx2, crate::arch::mldsa44::VG_MLDSA44_SIGN_MESSAGE_PREPARED_AVX2_FEATURES),
    sign_message_prepared_avx512: (crate::arch::mldsa44::vg_mldsa44_sign_message_prepared_avx512, crate::arch::mldsa44::VG_MLDSA44_SIGN_MESSAGE_PREPARED_AVX512_FEATURES),
    verify_message_prepared_avx2: (crate::arch::mldsa44::vg_mldsa44_verify_message_prepared_avx2, crate::arch::mldsa44::VG_MLDSA44_VERIFY_MESSAGE_PREPARED_AVX2_FEATURES),
    verify_message_prepared_avx512: (crate::arch::mldsa44::vg_mldsa44_verify_message_prepared_avx512, crate::arch::mldsa44::VG_MLDSA44_VERIFY_MESSAGE_PREPARED_AVX512_FEATURES),
    pk: 1312,
    sk: 2560,
    sig: 2420,
    prepared_sk: 14848,
    prepared_pk: 5408,
    scratch: 9728,
    message_scratch: 9856,
}
