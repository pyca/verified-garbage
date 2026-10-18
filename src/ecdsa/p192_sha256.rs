//! ECDSA over P-192 with HMAC-SHA-256 on the architectures other than
//! x86-64: `vg_ecdsa_p192_sha256_sign`, which calls `vg_ecdsa_p192_sign`, for each
//! implementation of SHA-256's compression function. On x86-64,
//! `super::any` signs with every hash function.

#![cfg(any(target_arch = "x86", target_arch = "aarch64", target_arch = "arm"))]

use super::{Error, P192, SignatureHash, sealed};
use crate::arch::ecdsa_p192_sha256::vg_ecdsa_p192_sha256_sign;
#[cfg(target_arch = "aarch64")]
use crate::arch::ecdsa_p192_sha256::vg_ecdsa_p192_sha256_sign_sha2;
#[cfg(target_arch = "x86")]
use crate::arch::ecdsa_p192_sha256::vg_ecdsa_p192_sha256_sign_shani;
use crate::hashes::sha256::{Sha256, Sha256Backend};
use crate::zeroize::zeroize;

impl sealed::Functions<P192> for Sha256 {
    fn sign(d: &[u8; 24], digest: &[u8; 32]) -> Result<[u8; 48], Error> {
        let sign = match Sha256Backend::select(crate::cpu::detected()) {
            Sha256Backend::Scalar => vg_ecdsa_p192_sha256_sign,
            #[cfg(target_arch = "aarch64")]
            Sha256Backend::Sha2 => vg_ecdsa_p192_sha256_sign_sha2,
            #[cfg(target_arch = "x86")]
            Sha256Backend::ShaNi => vg_ecdsa_p192_sha256_sign_shani,
        };
        let mut out = [0; 48];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 48 bytes, `d` for
        // reads of 24, `digest` of 32 and `scratch` for reads and writes of
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

    fn verify(q: &[u8; 49], digest: &[u8; 32], signature: &[u8; 48]) -> Result<(), Error> {
        super::p192::verify_with(q, digest.split_first_chunk::<24>().unwrap().0, signature)
    }
}

impl SignatureHash<P192> for Sha256 {}
