//! SLH-DSA-SHAKE-256s (FIPS 205), the stateless hash-based digital signature
//! algorithm over SHAKE256, at security category 5 (small signatures, slower signing).
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
    name: "SLH-DSA-SHAKE-256s",
    keygen: crate::arch::dispatch::slhdsa_shake_256s::vg_slhdsa_shake_256s_keygen_auto,
    sign: crate::arch::dispatch::slhdsa_shake_256s::vg_slhdsa_shake_256s_sign_auto,
    verify: crate::arch::dispatch::slhdsa_shake_256s::vg_slhdsa_shake_256s_verify_auto,
    n: 32,
    sig: 29792,
}
