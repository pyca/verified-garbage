//! ECDSA over P-192.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use super::table::{HmacHash, sign_with};
use super::{SignatureHash, sealed};
use crate::arch::ecdsa_p192::vg_ecdsa_p192_sign;
use crate::arch::ecdsa_p192::vg_ecdsa_p192_verify;
use crate::ec::P192;
use crate::error::{InvalidKey, InvalidSignature};

/// Whether `signature` verifies with `q` for the hash `digest`.
fn verify_with(q: &[u8; 49], digest: &[u8], signature: &[u8; 48]) -> Result<(), InvalidSignature> {
    let mut scratch = [0u64; 1024];
    // SAFETY: `q` is valid for reads of 49 bytes, `digest` of `digest.len()`,
    // `signature` of 48 and `scratch` for reads and writes of 8192; `scratch`
    // is a distinct object from the others, so it overlaps neither them nor the
    // call's stack frame, and, as Rust objects, none wraps around the address
    // space.
    let ok =
        unsafe { vg_ecdsa_p192_verify(q, digest.as_ptr(), digest.len(), signature, &mut scratch) };
    if ok == 1 {
        Ok(())
    } else {
        Err(InvalidSignature)
    }
}

impl<H: HmacHash> sealed::Functions<P192> for H {
    fn sign(d: &[u8; 24], digest: &H::Output) -> Result<[u8; 48], InvalidKey> {
        // SAFETY: `vg_ecdsa_p192_sign` needs no CPU feature.
        unsafe { sign_with::<H, 24, 48>(vg_ecdsa_p192_sign, d, digest) }
    }

    /// The verified function takes the hash itself, of any length, and
    /// uses as many of its leftmost bits as the order has (FIPS 186-5 §6.4.2).
    fn verify(
        q: &[u8; 49],
        digest: &H::Output,
        signature: &[u8; 48],
    ) -> Result<(), InvalidSignature> {
        verify_with(q, digest.as_ref(), signature)
    }
}

impl<H: HmacHash> SignatureHash<P192> for H {}
