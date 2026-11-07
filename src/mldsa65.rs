//! ML-DSA-65 (FIPS 204), the module-lattice-based digital signature algorithm,
//! at security category 3.
//!
//! A private key is the 32-byte seed `ξ` it is generated from
//! ([`SigningKey65::from_seed`]), which the caller generates with an approved
//! RBG; the expanded private key is never exposed. HashML-DSA (§5.4) is not
//! provided. [`SigningKey65::sign_mu`] and [`VerifyingKey65::verify_mu`] take a
//! message representative `μ` that the caller computes (formatting the message
//! and hashing the public key), and the caller supplies the signing randomness.
//! A key that signs or verifies many messages can be prepared for them
//! ([`SigningKey65::prepare`], [`VerifyingKey65::prepare`]), which may make
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
    name: "ML-DSA-65",
    signing_key: SigningKey65,
    verifying_key: VerifyingKey65,
    prepared_signing_key: PreparedSigningKey65,
    prepared_verifying_key: PreparedVerifyingKey65,
    keygen: crate::arch::dispatch::mldsa65::vg_mldsa65_keygen_auto,
    sign: crate::arch::dispatch::mldsa65::vg_mldsa65_sign_auto,
    verify: crate::arch::dispatch::mldsa65::vg_mldsa65_verify_auto,
    sign_message: crate::arch::dispatch::mldsa65::vg_mldsa65_sign_message_auto,
    verify_message_cached: crate::arch::dispatch::mldsa65::vg_mldsa65_verify_message_cached_auto,
    pk_tr: crate::arch::dispatch::mldsa65::vg_mldsa65_pk_tr_auto,
    prepare_sign: crate::arch::dispatch::mldsa65::vg_mldsa65_prepare_signing_key_auto,
    prepare_verify: crate::arch::dispatch::mldsa65::vg_mldsa65_prepare_verifying_key_auto,
    sign_message_prepared: crate::arch::dispatch::mldsa65::vg_mldsa65_sign_message_prepared_auto,
    verify_message_prepared: crate::arch::dispatch::mldsa65::vg_mldsa65_verify_message_prepared_auto,
    pk: 1952,
    sk: 4032,
    sig: 3309,
    prepared_sk: 21440,
    prepared_pk: 8096,
    scratch: 12928,
    message_scratch: 13056,
}
