//! AES-ECB (SP 800-38A §6.1) with 128-, 192- and 256-bit keys, in place
//! and without padding.
//!
//! ECB is the block cipher applied to each block on its own, so the whole
//! mode is verified assembly: `vg_aes_expand_key` (contract
//! `VG.Spec.Aes.expandKeyContract`) writes the key schedule, and
//! `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`
//! (`encryptBlocksContract`, `decryptBlocksContract`) replace each block
//! with its `CIPHER` or `INVCIPHER`, in constant time. This module checks
//! the lengths, which the assembly does not, and holds the key schedule.
//!
//! On x86-64 and x86, CPUs with AES-NI run the `_aesni` functions
//! (`crate::aes::Backend`; there is no VAES implementation of whole blocks
//! yet, so its CPUs run them too); on AArch64, CPUs with the AES
//! instructions run the `_aes` ones. Elsewhere, and on other CPUs, the
//! constant-time bitsliced implementation runs.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use crate::aes::Backend;
#[cfg(target_arch = "aarch64")]
use crate::arch::aes::{
    VG_AES_DECRYPT_BLOCKS_AES_FEATURES, VG_AES_ENCRYPT_BLOCKS_AES_FEATURES,
    vg_aes_decrypt_blocks_aes, vg_aes_encrypt_blocks_aes, vg_aes_expand_key_aes,
};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::aes::{
    VG_AES_DECRYPT_BLOCKS_AESNI_FEATURES, VG_AES_ENCRYPT_BLOCKS_AESNI_FEATURES,
    vg_aes_decrypt_blocks_aesni, vg_aes_encrypt_blocks_aesni, vg_aes_expand_key_aesni,
};
use crate::arch::aes::{vg_aes_decrypt_blocks, vg_aes_encrypt_blocks, vg_aes_expand_key};
use crate::cpu::{Features, detected};
use crate::zeroize::zeroize;

/// The instance of a function for `backend`: the scalar one, x86-64's or
/// x86's for AES-NI, or AArch64's for the AES instructions.
macro_rules! instance {
    ($backend:expr, $scalar:ident, $aesni:ident, $aes:ident) => {
        match $backend {
            Backend::Scalar => $scalar,
            // No VAES implementation of whole blocks yet.
            #[cfg(target_arch = "x86_64")]
            Backend::AesNi | Backend::Vaes => $aesni,
            #[cfg(target_arch = "x86")]
            Backend::AesNi => $aesni,
            #[cfg(target_arch = "aarch64")]
            Backend::Aes => $aes,
        }
    };
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its functions for whole blocks.
#[cfg(target_arch = "x86_64")]
fn select(f: Features) -> Backend {
    const AESNI: Features = Features::all(&[
        VG_AES_ENCRYPT_BLOCKS_AESNI_FEATURES,
        VG_AES_DECRYPT_BLOCKS_AESNI_FEATURES,
    ]);
    Backend::select_for(f, AESNI, AESNI)
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its functions for whole blocks.
#[cfg(target_arch = "x86")]
fn select(f: Features) -> Backend {
    const AESNI: Features = Features::all(&[
        VG_AES_ENCRYPT_BLOCKS_AESNI_FEATURES,
        VG_AES_DECRYPT_BLOCKS_AESNI_FEATURES,
    ]);
    Backend::select_for(f, AESNI)
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its functions for whole blocks.
#[cfg(target_arch = "aarch64")]
fn select(f: Features) -> Backend {
    const AES: Features = Features::all(&[
        VG_AES_ENCRYPT_BLOCKS_AES_FEATURES,
        VG_AES_DECRYPT_BLOCKS_AES_FEATURES,
    ]);
    Backend::select_for(f, AES)
}

/// The only implementation of AES on ARMv7.
#[cfg(target_arch = "arm")]
fn select(f: Features) -> Backend {
    Backend::select(f)
}

/// Why an AES-ECB operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key is not 16, 24 or 32 bytes long.
    InvalidKeyLength,
    /// The input length is not a multiple of 16 bytes.
    IncompleteBlock,
}

/// An expanded AES key for ECB encryption and decryption.
///
/// No padding is added or removed: each operation takes whole 16-byte
/// blocks. ECB encrypts equal blocks to equal blocks, so it hides little
/// of the structure of the plaintext; it is offered for compatibility.
pub struct AesEcb {
    /// The key schedule `vg_aes_expand_key` writes.
    schedule: [u8; 240],
    /// The number of rounds of AES: 10, 12 or 14.
    rounds: usize,
    /// The implementation of AES the functions called are.
    backend: Backend,
}

impl AesEcb {
    /// Expands a 16-, 24- or 32-byte key for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(Error::InvalidKeyLength);
        }
        let backend = select(detected());
        let expand = instance!(
            backend,
            vg_aes_expand_key,
            vg_aes_expand_key_aesni,
            vg_aes_expand_key_aes
        );
        let mut schedule = [0; 240];
        // SAFETY: the key is 16, 24 or 32 bytes long; the key and the
        // schedule are separate valid buffers of the sizes of the signature,
        // and `select` chose `expand` for the CPU's features. The function
        // zeroes its working space on its own stack before returning.
        unsafe { expand(key.as_ptr(), key.len(), &mut schedule) };
        Ok(Self {
            schedule,
            rounds: key.len() / 4 + 6,
            backend,
        })
    }

    /// Encrypts whole 16-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is not a
    /// multiple of 16.
    pub fn encrypt(&self, buffer: &mut [u8]) -> Result<(), Error> {
        let f = instance!(
            self.backend,
            vg_aes_encrypt_blocks,
            vg_aes_encrypt_blocks_aesni,
            vg_aes_encrypt_blocks_aes
        );
        self.crypt(buffer, f)
    }

    /// Decrypts whole 16-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is not a
    /// multiple of 16.
    pub fn decrypt(&self, buffer: &mut [u8]) -> Result<(), Error> {
        let f = instance!(
            self.backend,
            vg_aes_decrypt_blocks,
            vg_aes_decrypt_blocks_aesni,
            vg_aes_decrypt_blocks_aes
        );
        self.crypt(buffer, f)
    }

    fn crypt(&self, buffer: &mut [u8], f: Blocks) -> Result<(), Error> {
        if !buffer.len().is_multiple_of(16) {
            return Err(Error::IncompleteBlock);
        }
        let mut scratch = [0; 256];
        // SAFETY: `rounds` is 10, 12 or 14 and the schedule holds its key
        // schedule; the buffer holds `len / 16` whole blocks, and it, the
        // schedule and the scratch space are separate valid objects of the
        // sizes of the signature. `select` chose `f` for the CPU's features.
        unsafe {
            f(
                &self.schedule,
                self.rounds,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 16,
                &mut scratch,
            );
        }
        // The scratch space may hold the key schedule and the data.
        zeroize(&mut scratch);
        Ok(())
    }
}

/// The signature of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`.
#[cfg(target_arch = "x86_64")]
type Blocks =
    unsafe extern "sysv64" fn(*const [u8; 240], usize, *mut [u8; 16], usize, *mut [u64; 256]);
/// The signature of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`.
#[cfg(any(target_arch = "x86", target_arch = "aarch64", target_arch = "arm"))]
type Blocks = unsafe extern "C" fn(*const [u8; 240], usize, *mut [u8; 16], usize, *mut [u64; 256]);

impl Drop for AesEcb {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}

#[cfg(test)]
mod tests {
    use super::{AesEcb, select};
    use crate::cpu::detected;

    /// A new key uses the implementation chosen for the CPU's features.
    #[test]
    fn select_detected() {
        for len in [16, 24, 32] {
            assert_eq!(
                AesEcb::new(&[0; 32][..len]).unwrap().backend,
                select(detected())
            );
        }
    }

    /// Each implementation is chosen for the features of its functions.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64"))]
    #[test]
    fn select_features() {
        use crate::aes::Backend;
        use crate::cpu::Features;
        assert_eq!(select(Features(0)), Backend::Scalar);
        #[cfg(target_arch = "x86_64")]
        {
            assert_eq!(select(Features::of(&["aes", "ssse3"])), Backend::AesNi);
            let vaes = Features::of(&["aes", "avx", "avx2", "ssse3", "vaes"]);
            assert_eq!(select(vaes), Backend::Vaes);
        }
        #[cfg(target_arch = "x86")]
        assert_eq!(select(Features::of(&["aes"])), Backend::AesNi);
        #[cfg(target_arch = "aarch64")]
        assert_eq!(select(Features::of(&["aes"])), Backend::Aes);
    }
}
