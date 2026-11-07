//! ECDSA over brainpoolP512r1.

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
use crate::arch::dispatch::ecdsa_brainpoolp512r1::{
    vg_ecdsa_brainpoolp512r1_sign_auto, vg_ecdsa_brainpoolp512r1_verify_auto,
};
use crate::ec::BrainpoolP512r1;
use crate::error::{InvalidKey, InvalidSignature};

/// Whether `signature` verifies with `q` for the hash `digest`.
fn verify_with(
    q: &[u8; 129],
    digest: &[u8],
    signature: &[u8; 128],
) -> Result<(), InvalidSignature> {
    let mut scratch = [0u64; 1024];
    // SAFETY: `q` is valid for reads of 129 bytes, `digest` of `digest.len()`,
    // `signature` of 128 and `scratch` for reads and writes of 8192; `scratch`
    // is a distinct object from the others, so it overlaps neither them nor the
    // call's stack frame, and, as Rust objects, none wraps around the address
    // space. The dispatcher calls only an implementation the CPU has the
    // features of.
    let ok = unsafe {
        vg_ecdsa_brainpoolp512r1_verify_auto(
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

impl<H: HmacHash> sealed::Functions<BrainpoolP512r1> for H {
    fn sign(d: &[u8; 64], digest: &H::Output) -> Result<[u8; 128], InvalidKey> {
        sign_with::<H, 64, 128>(
            |out, d, digest, scratch, table| {
                // SAFETY: as `sign_with` says of its arguments; the dispatcher
                // calls only an implementation the CPU has the features of.
                unsafe {
                    vg_ecdsa_brainpoolp512r1_sign_auto(
                        out,
                        d,
                        digest.as_ptr(),
                        digest.len(),
                        scratch,
                        table,
                    )
                }
            },
            d,
            digest,
        )
    }

    /// The verified function takes the hash itself, of any length, and
    /// uses as many of its leftmost bits as the order has (FIPS 186-5 §6.4.2).
    fn verify(
        q: &[u8; 129],
        digest: &H::Output,
        signature: &[u8; 128],
    ) -> Result<(), InvalidSignature> {
        verify_with(q, digest.as_ref(), signature)
    }
}

impl<H: HmacHash> SignatureHash<BrainpoolP512r1> for H {}
