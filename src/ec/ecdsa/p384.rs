//! ECDSA over P-384.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use super::table::{HmacHash, SignFn, sign_with};
use super::{SignatureHash, sealed};
use crate::arch::dispatch::ecdsa_p384::vg_ecdsa_p384_verify_auto;
use crate::arch::ecdsa_p384::vg_ecdsa_p384_sign;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p384::vg_ecdsa_p384_sign_adx;
#[cfg(target_arch = "arm")]
use crate::arch::ecdsa_p384::vg_ecdsa_p384_sign_umaal;
use crate::cpu::detected;
use crate::ec::P384;
use crate::ec::p384::Mul;
use crate::error::{InvalidKey, InvalidSignature};

/// Whether `signature` verifies with `q` for the hash `digest`.
fn verify_with(q: &[u8; 97], digest: &[u8], signature: &[u8; 96]) -> Result<(), InvalidSignature> {
    let mut scratch = [0u64; 1024];
    // SAFETY: `q` is valid for reads of 97 bytes, `digest` of `digest.len()`,
    // `signature` of 96 and `scratch` for reads and writes of 8192; `scratch`
    // is a distinct object from the others, so it overlaps neither them nor the
    // call's stack frame, and, as Rust objects, none wraps around the address
    // space. The dispatcher calls only an implementation the CPU has the
    // features of.
    let ok = unsafe {
        vg_ecdsa_p384_verify_auto(q, digest.as_ptr(), digest.len(), signature, &mut scratch)
    };
    if ok == 1 {
        Ok(())
    } else {
        Err(InvalidSignature)
    }
}

impl<H: HmacHash> sealed::Functions<P384> for H {
    fn sign(d: &[u8; 48], digest: &H::Output) -> Result<[u8; 96], InvalidKey> {
        let f = detected();
        let sign: SignFn<48, 96> = match Mul::select(f) {
            Mul::Baseline => vg_ecdsa_p384_sign,
            #[cfg(target_arch = "x86_64")]
            Mul::Adx => vg_ecdsa_p384_sign_adx,
            #[cfg(target_arch = "arm")]
            Mul::Umaal => vg_ecdsa_p384_sign_umaal,
        };
        // SAFETY: `sign` needs no CPU feature that the multiplications
        // selected for this CPU do not.
        unsafe { sign_with::<H, 48, 96>(sign, f, d, digest) }
    }

    /// The verified function takes the hash itself, of any length, and
    /// uses as many of its leftmost bits as the order has (FIPS 186-5 §6.4.2).
    fn verify(
        q: &[u8; 97],
        digest: &H::Output,
        signature: &[u8; 96],
    ) -> Result<(), InvalidSignature> {
        verify_with(q, digest.as_ref(), signature)
    }
}

impl<H: HmacHash> SignatureHash<P384> for H {}
