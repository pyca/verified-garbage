//! SLH-DSA-SHAKE-256f (FIPS 205), the stateless hash-based digital signature
//! algorithm over SHAKE256, at security category 5 (fast signing, larger signatures).
//!
//! Keys are `SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root` and `PK.seed ‖ PK.root`
//! (FIPS 205 §9.1); [`SigningKey::generate`] draws the seeds from the
//! operating system, and [`SigningKey::from_seeds`] takes them from the
//! caller. Signing is the pure `slh_sign` with a context string, hedged
//! ([`SigningKey::sign`]) or deterministic; HashSLH-DSA is not provided.
//! Signing's timing may depend on the signature and the message digest it
//! signs, both public once the signature is.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

crate::slhdsa_common::slh_dsa! {
    name: "SLH-DSA-SHAKE-256f",
    keygen: crate::arch::dispatch::slhdsa_shake_256f::vg_slhdsa_shake_256f_keygen_auto,
    sign: crate::arch::dispatch::slhdsa_shake_256f::vg_slhdsa_shake_256f_sign_auto,
    verify: crate::arch::dispatch::slhdsa_shake_256f::vg_slhdsa_shake_256f_verify_auto,
    n: 32,
    sig: 49856,
}
