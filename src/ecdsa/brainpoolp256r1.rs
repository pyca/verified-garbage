//! ECDSA over brainpoolP256r1: deterministic signatures with HMAC-SHA-256
//! (`vg_ecdsa_brainpoolp256r1_sha256_sign`), public
//! keys (`vg_ec_brainpoolp256r1_public_key`), and verification (`vg_ecdsa_brainpoolp256r1_verify`),
//! and their `_umaal` variants on ARMv7 CPUs with the features their
//! `_FEATURES` constants name.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use super::{BrainpoolP256r1, Error, SignatureHash, SigningKey, sealed};
use crate::arch::ecdsa_brainpoolp256r1::vg_ecdsa_brainpoolp256r1_verify;
#[cfg(target_arch = "arm")]
use crate::arch::ecdsa_brainpoolp256r1::vg_ecdsa_brainpoolp256r1_verify_umaal;
use crate::arch::ecdsa_brainpoolp256r1_sha256::vg_ecdsa_brainpoolp256r1_sha256_sign;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_brainpoolp256r1_sha256::vg_ecdsa_brainpoolp256r1_sha256_sign_avx2;
#[cfg(target_arch = "aarch64")]
use crate::arch::ecdsa_brainpoolp256r1_sha256::vg_ecdsa_brainpoolp256r1_sha256_sign_sha2;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::ecdsa_brainpoolp256r1_sha256::vg_ecdsa_brainpoolp256r1_sha256_sign_shani;
#[cfg(target_arch = "arm")]
use crate::arch::ecdsa_brainpoolp256r1_sha256::vg_ecdsa_brainpoolp256r1_sha256_sign_umaal;
use crate::cpu::detected;
use crate::ec::brainpoolp256r1::{Mul, public_key};
use crate::hashes::sha256::{Sha256, Sha256Backend};
use crate::zeroize::zeroize;

impl SigningKey<BrainpoolP256r1> {
    /// The public key `Q = dG`, in the uncompressed form of SEC 1 §2.3.3:
    /// `04 ‖ x ‖ y`, each coordinate 32 bytes, most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<[u8; 65], Error> {
        public_key(&self.d).ok_or(Error::InvalidKey)
    }
}

impl sealed::Functions<BrainpoolP256r1> for Sha256 {
    fn sign(d: &[u8; 32], digest: &[u8; 32]) -> Result<[u8; 64], Error> {
        let f = detected();
        let sign = match (Sha256Backend::select(f), Mul::select(f)) {
            (Sha256Backend::Scalar, Mul::Baseline) => vg_ecdsa_brainpoolp256r1_sha256_sign,
            #[cfg(target_arch = "aarch64")]
            (Sha256Backend::Sha2, Mul::Baseline) => vg_ecdsa_brainpoolp256r1_sha256_sign_sha2,
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            (Sha256Backend::ShaNi, Mul::Baseline) => vg_ecdsa_brainpoolp256r1_sha256_sign_shani,
            #[cfg(target_arch = "x86_64")]
            (Sha256Backend::Avx2, Mul::Baseline) => vg_ecdsa_brainpoolp256r1_sha256_sign_avx2,
            #[cfg(target_arch = "arm")]
            (Sha256Backend::Scalar, Mul::Umaal) => vg_ecdsa_brainpoolp256r1_sha256_sign_umaal,
        };
        let mut out = [0; 64];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 64 bytes, `d` and
        // `digest` for reads of 32 and `scratch` for reads and writes of
        // 8192; `out` and `scratch` are distinct objects from each other and
        // the others, so none overlaps another or the call's stack frame,
        // and, as Rust objects, none wraps around the address space. `sign`
        // needs no CPU feature that the implementation of SHA-256 and the
        // multiplications selected for this CPU do not.
        let ok = unsafe { sign(&mut out, d, digest, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }

    fn verify(q: &[u8; 65], digest: &[u8; 32], signature: &[u8; 64]) -> Result<(), Error> {
        let mut scratch = [0u64; 1024];
        let ok = match Mul::select(detected()) {
            // SAFETY: `q` is valid for reads of 65 bytes, `digest` of 32,
            // `signature` of 64 and `scratch` for reads and writes of 8192;
            // `scratch` is a distinct object from the others, so it overlaps
            // neither them nor the call's stack frame, and, as Rust objects,
            // none wraps around the address space.
            Mul::Baseline => unsafe {
                vg_ecdsa_brainpoolp256r1_verify(q, digest, signature, &mut scratch)
            },
            // SAFETY: as for `Mul::Baseline`, and the CPU has `umaal`
            // (`Mul::select`).
            #[cfg(target_arch = "arm")]
            Mul::Umaal => unsafe {
                vg_ecdsa_brainpoolp256r1_verify_umaal(q, digest, signature, &mut scratch)
            },
        };
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::InvalidSignature)
        }
    }
}

impl SignatureHash<BrainpoolP256r1> for Sha256 {}
