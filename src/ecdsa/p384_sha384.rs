//! ECDSA over P-384 with HMAC-SHA-384 on the architectures other than
//! x86-64: `vg_ecdsa_p384_sha384_sign`, which calls `vg_ecdsa_p384_sign`, for each
//! implementation of SHA-384's compression function. On x86-64,
//! `super::any` signs with every hash function.

#![cfg(any(target_arch = "x86", target_arch = "aarch64", target_arch = "arm"))]

use super::{Error, P384, SignatureHash, sealed};
use crate::arch::ecdsa_p384_sha384::vg_ecdsa_p384_sha384_sign;
#[cfg(target_arch = "aarch64")]
use crate::arch::ecdsa_p384_sha384::vg_ecdsa_p384_sha384_sign_sha3;
use crate::cpu::detected;
use crate::ec::p384::Mul;
use crate::hashes::sha384::{Sha384, Sha384Backend};
use crate::zeroize::zeroize;

impl sealed::Functions<P384> for Sha384 {
    fn sign(d: &[u8; 48], digest: &[u8; 48]) -> Result<[u8; 96], Error> {
        let f = detected();
        let sign = match (Sha384Backend::select(f), Mul::select(f)) {
            (Sha384Backend::Scalar, Mul::Baseline) => vg_ecdsa_p384_sha384_sign,
            #[cfg(target_arch = "aarch64")]
            (Sha384Backend::Sha3, Mul::Baseline) => vg_ecdsa_p384_sha384_sign_sha3,
        };
        let mut out = [0; 96];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 96 bytes, `d` and
        // `digest` for reads of 48 and `scratch` for reads and writes of
        // 8192; `out` and `scratch` are distinct objects from each other and
        // the others, so none overlaps another or the call's stack frame,
        // and, as Rust objects, none wraps around the address space. `sign`
        // needs no CPU feature that the implementation of SHA-384 and the
        // multiplications selected for this CPU do not.
        let ok = unsafe { sign(&mut out, d, digest, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }

    fn verify(q: &[u8; 97], digest: &[u8; 48], signature: &[u8; 96]) -> Result<(), Error> {
        super::p384::verify_with(q, digest, signature)
    }
}

impl SignatureHash<P384> for Sha384 {}
