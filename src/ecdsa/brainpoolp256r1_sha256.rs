//! ECDSA over brainpoolP256r1 with HMAC-SHA-256 on the architectures other than
//! x86-64: `vg_ecdsa_brainpoolp256r1_sha256_sign`, which calls `vg_ecdsa_brainpoolp256r1_sign`, for each
//! implementation of SHA-256's compression function. On x86-64,
//! `super::any` signs with every hash function.

#![cfg(any(target_arch = "x86", target_arch = "aarch64", target_arch = "arm"))]

use super::{BrainpoolP256r1, Error, SignatureHash, sealed};
use crate::arch::ecdsa_brainpoolp256r1_sha256::vg_ecdsa_brainpoolp256r1_sha256_sign;
#[cfg(target_arch = "aarch64")]
use crate::arch::ecdsa_brainpoolp256r1_sha256::vg_ecdsa_brainpoolp256r1_sha256_sign_sha2;
#[cfg(target_arch = "x86")]
use crate::arch::ecdsa_brainpoolp256r1_sha256::vg_ecdsa_brainpoolp256r1_sha256_sign_shani;
use crate::hashes::sha256::{Sha256, Sha256Backend};
use crate::zeroize::zeroize;

impl sealed::Functions<BrainpoolP256r1> for Sha256 {
    fn sign(d: &[u8; 32], digest: &[u8; 32]) -> Result<[u8; 64], Error> {
        let sign = match Sha256Backend::select(crate::cpu::detected()) {
            Sha256Backend::Scalar => vg_ecdsa_brainpoolp256r1_sha256_sign,
            #[cfg(target_arch = "aarch64")]
            Sha256Backend::Sha2 => vg_ecdsa_brainpoolp256r1_sha256_sign_sha2,
            #[cfg(target_arch = "x86")]
            Sha256Backend::ShaNi => vg_ecdsa_brainpoolp256r1_sha256_sign_shani,
        };
        let mut out = [0; 64];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 64 bytes, `d` and
        // `digest` for reads of 32 and `scratch` for reads and writes of
        // 8192; `out` and `scratch` are distinct objects from each other and
        // the others, so none overlaps another or the call's stack frame,
        // and, as Rust objects, none wraps around the address space. `sign`
        // needs no CPU feature that the implementation of SHA-256 selected
        // for this CPU does not.
        let ok = unsafe { sign(&mut out, d, digest, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }

    fn verify(q: &[u8; 65], digest: &[u8; 32], signature: &[u8; 64]) -> Result<(), Error> {
        super::brainpoolp256r1::verify_with(q, digest, signature)
    }
}

impl SignatureHash<BrainpoolP256r1> for Sha256 {}
