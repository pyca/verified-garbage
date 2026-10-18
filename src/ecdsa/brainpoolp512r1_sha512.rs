//! ECDSA over brainpoolP512r1 with HMAC-SHA-512 on the architectures other than
//! x86-64: `vg_ecdsa_brainpoolp512r1_sha512_sign`, which calls `vg_ecdsa_brainpoolp512r1_sign`, for each
//! implementation of SHA-512's compression function. On x86-64,
//! `super::any` signs with every hash function.

#![cfg(any(target_arch = "x86", target_arch = "aarch64", target_arch = "arm"))]

use super::{BrainpoolP512r1, Error, SignatureHash, sealed};
use crate::arch::ecdsa_brainpoolp512r1_sha512::vg_ecdsa_brainpoolp512r1_sha512_sign;
#[cfg(target_arch = "aarch64")]
use crate::arch::ecdsa_brainpoolp512r1_sha512::vg_ecdsa_brainpoolp512r1_sha512_sign_sha3;
use crate::hashes::sha512::{Sha512, Sha512Backend};
use crate::zeroize::zeroize;

impl sealed::Functions<BrainpoolP512r1> for Sha512 {
    fn sign(d: &[u8; 64], digest: &[u8; 64]) -> Result<[u8; 128], Error> {
        let sign = match Sha512Backend::select(crate::cpu::detected()) {
            Sha512Backend::Scalar => vg_ecdsa_brainpoolp512r1_sha512_sign,
            #[cfg(target_arch = "aarch64")]
            Sha512Backend::Sha3 => vg_ecdsa_brainpoolp512r1_sha512_sign_sha3,
        };
        let mut out = [0; 128];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 128 bytes, `d` and
        // `digest` for reads of 64 and `scratch` for reads and writes of
        // 8192; `out` and `scratch` are distinct objects from each other and
        // the others, so none overlaps another or the call's stack frame,
        // and, as Rust objects, none wraps around the address space. `sign`
        // needs no CPU feature that the implementation of SHA-512 selected
        // for this CPU does not.
        let ok = unsafe { sign(&mut out, d, digest, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }

    fn verify(q: &[u8; 129], digest: &[u8; 64], signature: &[u8; 128]) -> Result<(), Error> {
        super::brainpoolp512r1::verify_with(q, digest, signature)
    }
}

impl SignatureHash<BrainpoolP512r1> for Sha512 {}
