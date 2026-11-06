//! ECDSA over P-224.

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
use crate::arch::ecdsa_p224::vg_ecdsa_p224_sign;
use crate::arch::ecdsa_p224::vg_ecdsa_p224_verify;
#[cfg(target_arch = "arm")]
use crate::arch::ecdsa_p224::{vg_ecdsa_p224_sign_umaal, vg_ecdsa_p224_verify_umaal};
use crate::cpu::detected;
use crate::ec::P224;
use crate::ec::p224::Mul;
use crate::error::{InvalidKey, InvalidSignature};

/// Whether `signature` verifies with `q` for the hash `digest`.
fn verify_with(q: &[u8; 57], digest: &[u8], signature: &[u8; 56]) -> Result<(), InvalidSignature> {
    let mut scratch = [0u64; 1024];
    let ok = match Mul::select(detected()) {
        // SAFETY: `q` is valid for reads of 57 bytes, `digest` of `digest.len()`,
        // `signature` of 56 and `scratch` for reads and writes of 8192; `scratch`
        // is a distinct object from the others, so it overlaps neither them nor the
        // call's stack frame, and, as Rust objects, none wraps around the address
        // space.
        Mul::Baseline => unsafe {
            vg_ecdsa_p224_verify(q, digest.as_ptr(), digest.len(), signature, &mut scratch)
        },
        // SAFETY: as for `Mul::Baseline`, and the CPU has `umaal`
        // (`Mul::select`).
        #[cfg(target_arch = "arm")]
        Mul::Umaal => unsafe {
            vg_ecdsa_p224_verify_umaal(q, digest.as_ptr(), digest.len(), signature, &mut scratch)
        },
    };
    if ok == 1 {
        Ok(())
    } else {
        Err(InvalidSignature)
    }
}

impl<H: HmacHash> sealed::Functions<P224> for H {
    fn sign(d: &[u8; 28], digest: &H::Output) -> Result<[u8; 56], InvalidKey> {
        let f = detected();
        let sign: SignFn<28, 56> = match Mul::select(f) {
            Mul::Baseline => vg_ecdsa_p224_sign,
            #[cfg(target_arch = "arm")]
            Mul::Umaal => vg_ecdsa_p224_sign_umaal,
        };
        // SAFETY: `sign` needs no CPU feature that the multiplications
        // selected for this CPU do not.
        unsafe { sign_with::<H, 28, 56>(sign, f, d, digest) }
    }

    /// The verified function takes the hash itself, of any length, and
    /// uses as many of its leftmost bits as the order has (FIPS 186-5 §6.4.2).
    fn verify(
        q: &[u8; 57],
        digest: &H::Output,
        signature: &[u8; 56],
    ) -> Result<(), InvalidSignature> {
        verify_with(q, digest.as_ref(), signature)
    }
}

impl<H: HmacHash> SignatureHash<P224> for H {}
