//! ECDSA over secp256k1: deterministic signatures with HMAC-SHA-256
//! (`vg_ecdsa_secp256k1_sha256_sign`, which calls `vg_ecdsa_secp256k1_sign`), public
//! keys (`vg_ec_secp256k1_public_key`), and verification (`vg_ecdsa_secp256k1_verify`).

#![cfg(target_arch = "x86_64")]

use super::{Error, Secp256k1, SignatureHash, SigningKey, sealed};
use crate::arch::ec_secp256k1::vg_ec_secp256k1_public_key;
use crate::arch::ecdsa_secp256k1::vg_ecdsa_secp256k1_verify;
use crate::arch::ecdsa_secp256k1_sha256::vg_ecdsa_secp256k1_sha256_sign;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_secp256k1_sha256::{
    vg_ecdsa_secp256k1_sha256_sign_avx2, vg_ecdsa_secp256k1_sha256_sign_shani,
};
use crate::hashes::sha256::{Sha256, Sha256Backend};
use crate::zeroize::zeroize;

impl SigningKey<Secp256k1> {
    /// The public key `Q = dG`, in the uncompressed form of SEC 1 §2.3.3:
    /// `04 ‖ x ‖ y`, each coordinate 32 bytes, most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<[u8; 65], Error> {
        let mut out = [0; 65];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 65 bytes, `self.d`
        // for reads of 32 and `scratch` for reads and writes of 8192; `out`
        // and `scratch` are distinct objects from each other and `self.d`,
        // so none overlaps another or the call's stack frame, and, as Rust
        // objects, none wraps around the address space.
        let ok = unsafe { vg_ec_secp256k1_public_key(&mut out, &self.d, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }
}

impl sealed::Functions<Secp256k1> for Sha256 {
    fn sign(d: &[u8; 32], digest: &[u8; 32]) -> Result<[u8; 64], Error> {
        let sign = match Sha256Backend::select(crate::cpu::detected()) {
            Sha256Backend::Scalar => vg_ecdsa_secp256k1_sha256_sign,
            #[cfg(target_arch = "x86_64")]
            Sha256Backend::ShaNi => vg_ecdsa_secp256k1_sha256_sign_shani,
            #[cfg(target_arch = "x86_64")]
            Sha256Backend::Avx2 => vg_ecdsa_secp256k1_sha256_sign_avx2,
        };
        let mut out = [0; 64];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 64 bytes, `d` and
        // `digest` for reads of 32 and `scratch` for reads and writes of
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

    fn verify(q: &[u8; 65], digest: &[u8; 32], signature: &[u8; 64]) -> Result<(), Error> {
        let mut scratch = [0u64; 1024];
        // SAFETY: `q` is valid for reads of 65 bytes, `digest` of 32,
        // `signature` of 64 and `scratch` for reads and writes of 8192;
        // `scratch` is a distinct object from the others, so it overlaps
        // neither them nor the call's stack frame, and, as Rust objects,
        // none wraps around the address space.
        let ok = unsafe { vg_ecdsa_secp256k1_verify(q, digest, signature, &mut scratch) };
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::InvalidSignature)
        }
    }
}

impl SignatureHash<Secp256k1> for Sha256 {}
