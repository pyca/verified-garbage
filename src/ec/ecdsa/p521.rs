//! ECDSA over P-521.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use super::table::{HmacHash, sign_with};
use super::{SignatureHash, sealed};
use crate::align::CacheAligned;
use crate::arch::dispatch::ecdsa_p521::{vg_ecdsa_p521_sign_auto, vg_ecdsa_p521_verify_auto};
use crate::ec::P521;
use crate::error::{InvalidKey, InvalidSignature};

/// Whether `signature` verifies with `q` for the hash `digest`.
fn verify_with(
    dit: crate::dit::Dit<'_>,
    q: &[u8; 133],
    digest: &[u8],
    signature: &[u8; 132],
) -> Result<(), InvalidSignature> {
    let mut scratch = CacheAligned([0u64; 1024]);
    // SAFETY: `q` is valid for reads of 133 bytes, `digest` of `digest.len()`,
    // `signature` of 132 and `scratch` for reads and writes of 8192; `scratch`
    // is a distinct object from the others, so it overlaps neither them nor the
    // call's stack frame, and, as Rust objects, none wraps around the address
    // space. The dispatcher calls only an implementation the CPU has the
    // features of.
    let ok = unsafe {
        vg_ecdsa_p521_verify_auto(
            dit,
            q,
            digest.as_ptr(),
            digest.len(),
            signature,
            &mut scratch.0,
        )
    };
    if ok == 1 {
        Ok(())
    } else {
        Err(InvalidSignature)
    }
}

impl<H: HmacHash> sealed::Functions<P521> for H {
    fn sign(
        dit: crate::dit::Dit<'_>,
        d: &[u8; 66],
        digest: &H::Output,
    ) -> Result<[u8; 132], InvalidKey> {
        sign_with::<H, 66, 132>(
            dit,
            |dit, out, d, digest, scratch, table| {
                // SAFETY: as `sign_with` says of its arguments; the dispatcher
                // calls only an implementation the CPU has the features of.
                unsafe {
                    vg_ecdsa_p521_sign_auto(
                        dit,
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
        dit: crate::dit::Dit<'_>,
        q: &[u8; 133],
        digest: &H::Output,
        signature: &[u8; 132],
    ) -> Result<(), InvalidSignature> {
        verify_with(dit, q, digest.as_ref(), signature)
    }
}

impl<H: HmacHash> SignatureHash<P521> for H {}
