//! ECDSA over brainpoolP256r1.

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
use crate::arch::dispatch::ecdsa_brainpoolp256r1::vg_ecdsa_brainpoolp256r1_verify_auto;
use crate::arch::ecdsa_brainpoolp256r1::vg_ecdsa_brainpoolp256r1_sign;
#[cfg(target_arch = "arm")]
use crate::arch::ecdsa_brainpoolp256r1::vg_ecdsa_brainpoolp256r1_sign_umaal;
use crate::cpu::detected;
use crate::ec::BrainpoolP256r1;
use crate::ec::brainpoolp256r1::Mul;
use crate::error::{InvalidKey, InvalidSignature};

/// Whether `signature` verifies with `q` for the hash `digest`.
fn verify_with(q: &[u8; 65], digest: &[u8], signature: &[u8; 64]) -> Result<(), InvalidSignature> {
    let mut scratch = [0u64; 1024];
    // SAFETY: `q` is valid for reads of 65 bytes, `digest` of `digest.len()`,
    // `signature` of 64 and `scratch` for reads and writes of 8192; `scratch`
    // is a distinct object from the others, so it overlaps neither them nor the
    // call's stack frame, and, as Rust objects, none wraps around the address
    // space. The dispatcher calls only an implementation the CPU has the
    // features of.
    let ok = unsafe {
        vg_ecdsa_brainpoolp256r1_verify_auto(
            q,
            digest.as_ptr(),
            digest.len(),
            signature,
            &mut scratch,
        )
    };
    if ok == 1 {
        Ok(())
    } else {
        Err(InvalidSignature)
    }
}

impl<H: HmacHash> sealed::Functions<BrainpoolP256r1> for H {
    fn sign(d: &[u8; 32], digest: &H::Output) -> Result<[u8; 64], InvalidKey> {
        let f = detected();
        let sign: SignFn<32, 64> = match Mul::select(f) {
            Mul::Baseline => vg_ecdsa_brainpoolp256r1_sign,
            #[cfg(target_arch = "arm")]
            Mul::Umaal => vg_ecdsa_brainpoolp256r1_sign_umaal,
        };
        // SAFETY: `sign` needs no CPU feature that the multiplications
        // selected for this CPU do not.
        unsafe { sign_with::<H, 32, 64>(sign, d, digest) }
    }

    /// The verified function takes the hash itself, of any length, and
    /// uses as many of its leftmost bits as the order has (FIPS 186-5 §6.4.2).
    fn verify(
        q: &[u8; 65],
        digest: &H::Output,
        signature: &[u8; 64],
    ) -> Result<(), InvalidSignature> {
        verify_with(q, digest.as_ref(), signature)
    }
}

impl<H: HmacHash> SignatureHash<BrainpoolP256r1> for H {}
