//! ECDSA over P-224: deterministic signatures with HMAC-SHA-224
//! (`vg_ecdsa_p224_sha224_sign`, which calls `vg_ecdsa_p224_sign`), public
//! keys (`vg_ec_p224_public_key`), and verification (`vg_ecdsa_p224_verify`).

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use super::{Error, P224, SignatureHash, SigningKey, sealed};
use crate::arch::ec_p224::vg_ec_p224_public_key;
use crate::arch::ecdsa_p224::vg_ecdsa_p224_verify;
use crate::arch::ecdsa_p224_sha224::vg_ecdsa_p224_sha224_sign;
#[cfg(target_arch = "aarch64")]
use crate::arch::ecdsa_p224_sha224::vg_ecdsa_p224_sha224_sign_sha2;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p224_sha224::{
    vg_ecdsa_p224_sha224_sign_avx2, vg_ecdsa_p224_sha224_sign_shani,
};
use crate::hashes::sha224::{Sha224, Sha224Backend};
use crate::zeroize::zeroize;

impl SigningKey<P224> {
    /// The public key `Q = dG`, in the uncompressed form of SEC 1 §2.3.3:
    /// `04 ‖ x ‖ y`, each coordinate 28 bytes, most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<[u8; 57], Error> {
        let mut out = [0; 57];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 57 bytes, `self.d`
        // for reads of 28 and `scratch` for reads and writes of 8192; `out`
        // and `scratch` are distinct objects from each other and `self.d`,
        // so none overlaps another or the call's stack frame, and, as Rust
        // objects, none wraps around the address space.
        let ok = unsafe { vg_ec_p224_public_key(&mut out, &self.d, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }
}

impl sealed::Functions<P224> for Sha224 {
    fn sign(d: &[u8; 28], digest: &[u8; 28]) -> Result<[u8; 56], Error> {
        let sign = match Sha224Backend::select(crate::cpu::detected()) {
            Sha224Backend::Scalar => vg_ecdsa_p224_sha224_sign,
            #[cfg(target_arch = "aarch64")]
            Sha224Backend::Sha2 => vg_ecdsa_p224_sha224_sign_sha2,
            #[cfg(target_arch = "x86_64")]
            Sha224Backend::ShaNi => vg_ecdsa_p224_sha224_sign_shani,
            #[cfg(target_arch = "x86_64")]
            Sha224Backend::Avx2 => vg_ecdsa_p224_sha224_sign_avx2,
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
        let mut scratch = [0u64; 1024];
        // SAFETY: `q` is valid for reads of 57 bytes, `digest` of 28,
        // `signature` of 56 and `scratch` for reads and writes of 8192;
        // `scratch` is a distinct object from the others, so it overlaps
        // neither them nor the call's stack frame, and, as Rust objects,
        // none wraps around the address space.
        let ok = unsafe { vg_ecdsa_p224_verify(q, digest, signature, &mut scratch) };
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::InvalidSignature)
        }
    }
}

impl SignatureHash<P224> for Sha224 {}
