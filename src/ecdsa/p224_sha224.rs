//! ECDSA over P-224 with HMAC-SHA-224 on the architectures other than
//! x86-64: `vg_ecdsa_p224_sha224_sign`, which calls `vg_ecdsa_p224_sign`, for each
//! implementation of SHA-224's compression function. On x86-64,
//! `super::any` signs with every hash function.

#![cfg(any(target_arch = "x86", target_arch = "aarch64", target_arch = "arm"))]

use super::{Error, P224, SignatureHash, sealed};
use crate::arch::ecdsa_p224_sha224::vg_ecdsa_p224_sha224_sign;
#[cfg(target_arch = "aarch64")]
use crate::arch::ecdsa_p224_sha224::vg_ecdsa_p224_sha224_sign_sha2;
#[cfg(target_arch = "x86")]
use crate::arch::ecdsa_p224_sha224::vg_ecdsa_p224_sha224_sign_shani;
use crate::hashes::sha224::{Sha224, Sha224Backend};
use crate::zeroize::zeroize;

impl sealed::Functions<P224> for Sha224 {
    fn sign(d: &[u8; 28], digest: &[u8; 28]) -> Result<[u8; 56], Error> {
        let sign = match Sha224Backend::select(crate::cpu::detected()) {
            Sha224Backend::Scalar => vg_ecdsa_p224_sha224_sign,
            #[cfg(target_arch = "aarch64")]
            Sha224Backend::Sha2 => vg_ecdsa_p224_sha224_sign_sha2,
            #[cfg(target_arch = "x86")]
            Sha224Backend::ShaNi => vg_ecdsa_p224_sha224_sign_shani,
        };
        let mut out = [0; 56];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 56 bytes, `d` and
        // `digest` for reads of 28 and `scratch` for reads and writes of
        // 8192; `out` and `scratch` are distinct objects from each other and
        // the others, so none overlaps another or the call's stack frame,
        // and, as Rust objects, none wraps around the address space. `sign`
        // needs no CPU feature that the implementation of SHA-224 selected
        // for this CPU does not.
        let ok = unsafe { sign(&mut out, d, digest, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }

    fn verify(q: &[u8; 57], digest: &[u8; 28], signature: &[u8; 56]) -> Result<(), Error> {
        super::p224::verify_with(q, digest, signature)
    }
}

impl SignatureHash<P224> for Sha224 {}
