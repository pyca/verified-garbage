//! ECDSA over P-521: deterministic signatures with HMAC-SHA-512
//! (`vg_ecdsa_p521_sha512_sign`, which calls `vg_ecdsa_p521_sign`), public
//! keys (`vg_ec_p521_public_key`), and verification (`vg_ecdsa_p521_verify`).

#![cfg(any(target_arch = "x86_64", target_arch = "x86", target_arch = "arm"))]

use super::{Error, P521, SignatureHash, SigningKey, sealed};
use crate::arch::ec_p521::vg_ec_p521_public_key;
use crate::arch::ecdsa_p521::vg_ecdsa_p521_verify;
use crate::arch::ecdsa_p521_sha512::vg_ecdsa_p521_sha512_sign;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p521_sha512::{
    vg_ecdsa_p521_sha512_sign_avx2, vg_ecdsa_p521_sha512_sign_shani,
};
use crate::hashes::sha512::{Sha512, Sha512Backend};
use crate::zeroize::zeroize;

impl SigningKey<P521> {
    /// The public key `Q = dG`, in the uncompressed form of SEC 1 §2.3.3:
    /// `04 ‖ x ‖ y`, each coordinate 66 bytes, most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<[u8; 133], Error> {
        let mut out = [0; 133];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 133 bytes, `self.d`
        // for reads of 66 and `scratch` for reads and writes of 8192; `out`
        // and `scratch` are distinct objects from each other and `self.d`,
        // so none overlaps another or the call's stack frame, and, as Rust
        // objects, none wraps around the address space.
        let ok = unsafe { vg_ec_p521_public_key(&mut out, &self.d, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }
}

/// The 66 bytes `vg_ecdsa_p521_verify` takes for a hash shorter than them:
/// the hash's integer shifted left by 7 bits, so that its leftmost 521 bits
/// are the hash's integer (FIPS 186-5 §6.4.1).
fn widen(digest: &[u8; 64]) -> [u8; 66] {
    let mut out = [0; 66];
    for (i, b) in digest.iter().enumerate() {
        out[i + 1] |= b >> 1;
        out[i + 2] |= b << 7;
    }
    out
}

impl sealed::Functions<P521> for Sha512 {
    fn sign(d: &[u8; 66], digest: &[u8; 64]) -> Result<[u8; 132], Error> {
        let sign = match Sha512Backend::select(crate::cpu::detected()) {
            Sha512Backend::Scalar => vg_ecdsa_p521_sha512_sign,
            #[cfg(target_arch = "x86_64")]
            Sha512Backend::ShaNi => vg_ecdsa_p521_sha512_sign_shani,
            #[cfg(target_arch = "x86_64")]
            Sha512Backend::Avx2 => vg_ecdsa_p521_sha512_sign_avx2,
        };
        let mut out = [0; 132];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 132 bytes, `d` for
        // reads of 66, `digest` of 64 and `scratch` for reads and writes of
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

    fn verify(q: &[u8; 133], digest: &[u8; 64], signature: &[u8; 132]) -> Result<(), Error> {
        let digest = widen(digest);
        let mut scratch = [0u64; 1024];
        // SAFETY: `q` is valid for reads of 133 bytes, `digest` of 66,
        // `signature` of 132 and `scratch` for reads and writes of 8192;
        // `scratch` is a distinct object from the others, so it overlaps
        // neither them nor the call's stack frame, and, as Rust objects,
        // none wraps around the address space.
        let ok = unsafe { vg_ecdsa_p521_verify(q, &digest, signature, &mut scratch) };
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::InvalidSignature)
        }
    }
}

impl SignatureHash<P521> for Sha512 {}
