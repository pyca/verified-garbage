//! Triple DES ECB (FIPS 46-3), in place and without padding.
//!
//! Key expansion and ECB encryption/decryption use verified primitives:
//! `vg_triple_des_expand_key`, `vg_triple_des_ecb_encrypt` and
//! `vg_triple_des_ecb_decrypt` (`VG.Spec.TripleDes.expandKeyContract`,
//! `ecbEncryptContract`, `ecbDecryptContract`). Each operation accepts
//! complete eight-byte blocks, including empty input.
//!
//! The variants of ECB encryption and decryption, with the same contracts,
//! are chosen by `Backend::select` on CPUs with the features their
//! `_FEATURES` constants name: on x86-64, `vg_triple_des_ecb_encrypt_avx512`
//! and `vg_triple_des_ecb_decrypt_avx512`, then the `_avx2` ones.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::triple_des::{
    VG_TRIPLE_DES_ECB_DECRYPT_AVX2_FEATURES, VG_TRIPLE_DES_ECB_DECRYPT_AVX512_FEATURES,
    VG_TRIPLE_DES_ECB_ENCRYPT_AVX2_FEATURES, VG_TRIPLE_DES_ECB_ENCRYPT_AVX512_FEATURES,
    vg_triple_des_ecb_decrypt_avx2, vg_triple_des_ecb_decrypt_avx512,
    vg_triple_des_ecb_encrypt_avx2, vg_triple_des_ecb_encrypt_avx512,
};
use crate::arch::triple_des::{
    vg_triple_des_ecb_decrypt, vg_triple_des_ecb_encrypt, vg_triple_des_expand_key,
};
use crate::cpu::detected;
use crate::zeroize::zeroize;
use verified_garbage_cpu::Features;

/// The implementations of ECB encryption and decryption.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Backend {
    /// The baseline implementation.
    Scalar,
    /// `_avx2`.
    #[cfg(target_arch = "x86_64")]
    Avx2,
    /// `_avx512`.
    #[cfg(target_arch = "x86_64")]
    Avx512,
}

impl Backend {
    /// The best implementation a CPU with the features `f` can run.
    #[cfg(target_arch = "x86_64")]
    pub(crate) fn select(f: Features) -> Backend {
        if f.contains(
            const {
                Features::all(&[
                    VG_TRIPLE_DES_ECB_ENCRYPT_AVX512_FEATURES,
                    VG_TRIPLE_DES_ECB_DECRYPT_AVX512_FEATURES,
                ])
            },
        ) {
            Backend::Avx512
        } else if f.contains(
            const {
                Features::all(&[
                    VG_TRIPLE_DES_ECB_ENCRYPT_AVX2_FEATURES,
                    VG_TRIPLE_DES_ECB_DECRYPT_AVX2_FEATURES,
                ])
            },
        ) {
            Backend::Avx2
        } else {
            Backend::Scalar
        }
    }

    /// The best implementation a CPU with the features `f` can run: there
    /// is only one here.
    #[cfg(not(target_arch = "x86_64"))]
    pub(crate) fn select(_: Features) -> Backend {
        Backend::Scalar
    }
}

/// Why a Triple DES ECB operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key does not contain 16 or 24 bytes.
    InvalidKeyLength,
    /// The input length is not a multiple of eight bytes.
    IncompleteBlock,
}

crate::error::impl_error! {
    Error {
        InvalidKeyLength => "invalid Triple DES key length",
        IncompleteBlock => "Triple DES-ECB input is not a whole number of blocks",
    }
}

/// An expanded Triple DES key for ECB encryption and decryption.
///
/// A 24-byte key encodes K1, K2 and K3. A 16-byte key encodes K1 and K2,
/// with K3 repeating K1. Each byte's parity bit is ignored; weak and
/// repeated component keys are accepted. No padding is added or removed.
pub struct TripleDesEcb {
    schedule: [u8; 384],
    backend: Backend,
}

impl TripleDesEcb {
    /// Expands a 16- or 24-byte key for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        if !matches!(key.len(), 16 | 24) {
            return Err(Error::InvalidKeyLength);
        }
        let mut schedule = [0; 384];
        // SAFETY: the key has a validated length; key and schedule are
        // separate valid buffers of the required sizes. The function zeroes
        // its working space on its own stack before returning.
        unsafe {
            vg_triple_des_expand_key(key.as_ptr(), key.len(), &mut schedule);
        }
        Ok(Self {
            schedule,
            backend: Backend::select(detected()),
        })
    }

    /// Encrypts complete eight-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn encrypt(&self, buffer: &mut [u8]) -> Result<(), Error> {
        self.crypt(buffer, true)
    }

    /// Decrypts complete eight-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn decrypt(&self, buffer: &mut [u8]) -> Result<(), Error> {
        self.crypt(buffer, false)
    }

    fn crypt(&self, buffer: &mut [u8], encrypt: bool) -> Result<(), Error> {
        if !buffer.len().is_multiple_of(8) {
            return Err(Error::IncompleteBlock);
        }
        let f = match (self.backend, encrypt) {
            (Backend::Scalar, true) => vg_triple_des_ecb_encrypt,
            (Backend::Scalar, false) => vg_triple_des_ecb_decrypt,
            #[cfg(target_arch = "x86_64")]
            (Backend::Avx2, true) => vg_triple_des_ecb_encrypt_avx2,
            #[cfg(target_arch = "x86_64")]
            (Backend::Avx2, false) => vg_triple_des_ecb_decrypt_avx2,
            #[cfg(target_arch = "x86_64")]
            (Backend::Avx512, true) => vg_triple_des_ecb_encrypt_avx512,
            #[cfg(target_arch = "x86_64")]
            (Backend::Avx512, false) => vg_triple_des_ecb_decrypt_avx512,
        };
        // SAFETY: buffer contains complete eight-byte blocks, including zero
        // blocks. The buffer and schedule are separate valid objects and do
        // not overlap the callee's stack. `Backend::select` chose `f` for the
        // CPU's features. The function zeroes its working space on its own
        // stack before returning.
        unsafe {
            f(&self.schedule, buffer.as_mut_ptr().cast(), buffer.len() / 8);
        }
        Ok(())
    }
}

impl Drop for TripleDesEcb {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}

#[cfg(test)]
mod tests {
    use super::{Backend, TripleDesEcb};
    use crate::cpu::detected;

    /// The implementation chosen for each set of features.
    #[test]
    fn select() {
        let best = TripleDesEcb::new(&[0; 24]).unwrap().backend;
        assert_eq!(best, Backend::select(detected()));
        #[cfg(target_arch = "x86_64")]
        {
            use crate::arch::triple_des::{
                VG_TRIPLE_DES_ECB_DECRYPT_AVX2_FEATURES, VG_TRIPLE_DES_ECB_DECRYPT_AVX512_FEATURES,
                VG_TRIPLE_DES_ECB_ENCRYPT_AVX2_FEATURES, VG_TRIPLE_DES_ECB_ENCRYPT_AVX512_FEATURES,
            };
            use verified_garbage_cpu::{Features, feature};
            assert_eq!(
                Backend::select(Features::all(&[
                    VG_TRIPLE_DES_ECB_ENCRYPT_AVX512_FEATURES,
                    VG_TRIPLE_DES_ECB_DECRYPT_AVX512_FEATURES,
                    VG_TRIPLE_DES_ECB_ENCRYPT_AVX2_FEATURES,
                    VG_TRIPLE_DES_ECB_DECRYPT_AVX2_FEATURES
                ])),
                Backend::Avx512
            );
            assert_eq!(
                Backend::select(Features::all(&[
                    VG_TRIPLE_DES_ECB_ENCRYPT_AVX2_FEATURES,
                    VG_TRIPLE_DES_ECB_DECRYPT_AVX2_FEATURES
                ])),
                Backend::Avx2
            );
            assert_eq!(Backend::select(Features(feature::AVX)), Backend::Scalar);
        }
    }
}
