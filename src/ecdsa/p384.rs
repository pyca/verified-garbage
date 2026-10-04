//! ECDSA over P-384: deterministic signatures with HMAC-SHA-384
//! (`vg_ecdsa_p384_sha384_sign`, which calls `vg_ecdsa_p384_sign`), public
//! keys (`vg_ec_p384_public_key`), and verification (`vg_ecdsa_p384_verify`).

#![cfg(target_arch = "x86_64")]

use super::{Error, P384, SignatureHash, SigningKey, sealed};
use crate::arch::ec_p384::vg_ec_p384_public_key;
use crate::arch::ecdsa_p384::vg_ecdsa_p384_verify;
use crate::arch::ecdsa_p384_sha384::{
    vg_ecdsa_p384_sha384_sign, vg_ecdsa_p384_sha384_sign_avx2, vg_ecdsa_p384_sha384_sign_shani,
};
use crate::hashes::sha384::{Sha384, Sha384Backend};
use crate::zeroize::zeroize;

impl SigningKey<P384> {
    /// The public key `Q = dG`, in the uncompressed form of SEC 1 §2.3.3:
    /// `04 ‖ x ‖ y`, each coordinate 48 bytes, most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<[u8; 97], Error> {
        let mut out = [0; 97];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 97 bytes, `self.d`
        // for reads of 48 and `scratch` for reads and writes of 8192; `out`
        // and `scratch` are distinct objects from each other and `self.d`,
        // so none overlaps another or the call's stack frame, and, as Rust
        // objects, none wraps around the address space.
        let ok = unsafe { vg_ec_p384_public_key(&mut out, &self.d, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }
}

impl sealed::Functions<P384> for Sha384 {
    fn sign(d: &[u8; 48], digest: &[u8; 48]) -> Result<[u8; 96], Error> {
        let sign = match Sha384Backend::select(crate::cpu::detected()) {
            Sha384Backend::Scalar => vg_ecdsa_p384_sha384_sign,
            Sha384Backend::ShaNi => vg_ecdsa_p384_sha384_sign_shani,
            Sha384Backend::Avx2 => vg_ecdsa_p384_sha384_sign_avx2,
        };
        let mut out = [0; 96];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 96 bytes, `d` and
        // `digest` for reads of 48 and `scratch` for reads and writes of
        // 8192; `out` and `scratch` are distinct objects from each other and
        // the others, so none overlaps another or the call's stack frame,
        // and, as Rust objects, none wraps around the address space. `sign`
        // needs no CPU feature that the implementation of SHA-384 selected
        // for this CPU does not.
        let ok = unsafe { sign(&mut out, d, digest, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }

    fn verify(q: &[u8; 97], digest: &[u8; 48], signature: &[u8; 96]) -> Result<(), Error> {
        let mut scratch = [0u64; 1024];
        // SAFETY: `q` is valid for reads of 97 bytes, `digest` of 48,
        // `signature` of 96 and `scratch` for reads and writes of 8192;
        // `scratch` is a distinct object from the others, so it overlaps
        // neither them nor the call's stack frame, and, as Rust objects,
        // none wraps around the address space.
        let ok = unsafe { vg_ecdsa_p384_verify(q, digest, signature, &mut scratch) };
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::InvalidSignature)
        }
    }
}

impl SignatureHash<P384> for Sha384 {}
