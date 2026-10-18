//! ECDSA over P-521 with HMAC-SHA-512 on the architectures other than
//! x86-64: `vg_ecdsa_p521_sha512_sign`, which calls `vg_ecdsa_p521_sign`, for each
//! implementation of SHA-512's compression function. On x86-64,
//! `super::any` signs with every hash function.

#![cfg(any(target_arch = "x86", target_arch = "aarch64", target_arch = "arm"))]

use super::{Error, P521, SignatureHash, sealed};
use crate::arch::ecdsa_p521_sha512::vg_ecdsa_p521_sha512_sign;
#[cfg(target_arch = "aarch64")]
use crate::arch::ecdsa_p521_sha512::vg_ecdsa_p521_sha512_sign_sha3;
use crate::cpu::detected;
use crate::ec::p521::Mul;
use crate::hashes::sha512::{Sha512, Sha512Backend};
use crate::zeroize::zeroize;

impl sealed::Functions<P521> for Sha512 {
    fn sign(d: &[u8; 66], digest: &[u8; 64]) -> Result<[u8; 132], Error> {
        let f = detected();
        let sign = match (Sha512Backend::select(f), Mul::select(f)) {
            (Sha512Backend::Scalar, Mul::Baseline) => vg_ecdsa_p521_sha512_sign,
            #[cfg(target_arch = "aarch64")]
            (Sha512Backend::Sha3, Mul::Baseline) => vg_ecdsa_p521_sha512_sign_sha3,
        };
        let mut out = [0; 132];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 132 bytes, `d` for
        // reads of 66, `digest` of 64 and `scratch` for reads and writes of
        // 8192; `out` and `scratch` are distinct objects from each other and
        // the others, so none overlaps another or the call's stack frame,
        // and, as Rust objects, none wraps around the address space. `sign`
        // needs no CPU feature that the implementation of SHA-512 and the
        // multiplications selected for this CPU do not.
        let ok = unsafe { sign(&mut out, d, digest, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }

    fn verify(q: &[u8; 133], digest: &[u8; 64], signature: &[u8; 132]) -> Result<(), Error> {
        super::p521::verify_with(q, &super::p521::widen(digest), signature)
    }
}

impl SignatureHash<P521> for Sha512 {}
