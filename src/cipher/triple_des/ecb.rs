//! Triple DES-ECB (FIPS 46-3), in place and without padding.

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
use crate::error::{IncompleteBlock, InvalidKeyLength};
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

/// An expanded Triple DES key for ECB encryption and decryption.
///
/// A 24-byte key encodes K1, K2 and K3. A 16-byte key encodes K1 and K2,
/// with K3 repeating K1. Each byte's parity bit is ignored; weak and
/// repeated component keys are accepted. No padding is added or removed.
///
/// ECB encrypts equal blocks to equal blocks, so it reveals patterns in the
/// data.
pub struct TripleDesEcb {
    schedule: [u8; 384],
    backend: Backend,
}

impl TripleDesEcb {
    /// Expands a 16- or 24-byte key for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 24) {
            return Err(InvalidKeyLength);
        }
        let mut schedule = [0; 384];
        // SAFETY: the key has a validated length; key and schedule are separate
        // valid buffers of the required sizes.
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
    pub fn encrypt(&self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        self.crypt(buffer, true)
    }

    /// Decrypts complete eight-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn decrypt(&self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        self.crypt(buffer, false)
    }

    fn crypt(&self, buffer: &mut [u8], encrypt: bool) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(8) {
            return Err(IncompleteBlock);
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
        // blocks. The buffer and schedule are separate valid objects and do not
        // overlap the callee's stack. `Backend::select` chose `f` for the CPU's
        // features.
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
