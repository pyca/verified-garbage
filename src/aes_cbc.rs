//! AES-CBC (SP 800-38A §6.2) with 128-, 192- and 256-bit keys, in place
//! and without padding.
//!
//! The whole mode is verified assembly: `vg_aes_expand_key` (contract
//! `VG.Spec.Aes.expandKeyContract`) writes the key schedule, and
//! `vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt` (`VG.Spec.Cbc.aesEncryptContract`,
//! `aesDecryptContract`) replace each block with its CBC encryption or
//! decryption and the chaining value with the last ciphertext block, in
//! constant time. They call `vg_aes_encrypt_blocks` or
//! `vg_aes_decrypt_blocks` on one block at a time. This module checks the
//! lengths, which the assembly does not, and holds the key schedule.
//!
//! On x86-64, CPUs with VAES and AVX2 run the `_vaes` functions, and other
//! CPUs with AES-NI the `_aesni` ones (`crate::aes::Backend`), as on x86; on
//! AArch64, CPUs with the AES instructions run the `_aes` ones. Elsewhere, and on other CPUs, the
//! constant-time bitsliced implementation runs.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use crate::aes::Backend;
use crate::arch::aes::vg_aes_expand_key;
#[cfg(target_arch = "aarch64")]
use crate::arch::aes::vg_aes_expand_key_aes;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::aes::vg_aes_expand_key_aesni;
#[cfg(target_arch = "aarch64")]
use crate::arch::aes_cbc::{
    VG_AES_CBC_DECRYPT_AES_FEATURES, VG_AES_CBC_ENCRYPT_AES_FEATURES, vg_aes_cbc_decrypt_aes,
    vg_aes_cbc_encrypt_aes,
};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::aes_cbc::{
    VG_AES_CBC_DECRYPT_AESNI_FEATURES, VG_AES_CBC_ENCRYPT_AESNI_FEATURES, vg_aes_cbc_decrypt_aesni,
    vg_aes_cbc_encrypt_aesni,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::aes_cbc::{
    VG_AES_CBC_DECRYPT_VAES_FEATURES, VG_AES_CBC_ENCRYPT_VAES_FEATURES, vg_aes_cbc_decrypt_vaes,
    vg_aes_cbc_encrypt_vaes,
};
use crate::arch::aes_cbc::{vg_aes_cbc_decrypt, vg_aes_cbc_encrypt};
use crate::cpu::{Features, detected};
use crate::zeroize::zeroize;

/// The instance of a function for `backend`: the scalar one, x86-64's or
/// x86's for AES-NI, x86-64's for VAES, or AArch64's for the AES instructions.
macro_rules! instance {
    ($backend:expr, $scalar:ident, $aesni:ident, $vaes:ident, $aes:ident) => {
        match $backend {
            Backend::Scalar => $scalar,
            #[cfg(target_arch = "x86_64")]
            Backend::AesNi => $aesni,
            #[cfg(target_arch = "x86_64")]
            Backend::Vaes => $vaes,
            #[cfg(target_arch = "x86")]
            Backend::AesNi => $aesni,
            #[cfg(target_arch = "aarch64")]
            Backend::Aes => $aes,
        }
    };
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its CBC functions.
#[cfg(target_arch = "x86_64")]
fn select(f: Features) -> Backend {
    const AESNI: Features = Features::all(&[
        VG_AES_CBC_ENCRYPT_AESNI_FEATURES,
        VG_AES_CBC_DECRYPT_AESNI_FEATURES,
    ]);
    const VAES: Features = Features::all(&[
        VG_AES_CBC_ENCRYPT_VAES_FEATURES,
        VG_AES_CBC_DECRYPT_VAES_FEATURES,
    ]);
    Backend::select_for(f, VAES, AESNI)
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its CBC functions.
#[cfg(target_arch = "x86")]
fn select(f: Features) -> Backend {
    const AESNI: Features = Features::all(&[
        VG_AES_CBC_ENCRYPT_AESNI_FEATURES,
        VG_AES_CBC_DECRYPT_AESNI_FEATURES,
    ]);
    Backend::select_for(f, AESNI)
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its CBC functions.
#[cfg(target_arch = "aarch64")]
fn select(f: Features) -> Backend {
    const AES: Features = Features::all(&[
        VG_AES_CBC_ENCRYPT_AES_FEATURES,
        VG_AES_CBC_DECRYPT_AES_FEATURES,
    ]);
    Backend::select_for(f, AES)
}

/// The only implementation of AES on ARMv7.
#[cfg(target_arch = "arm")]
fn select(f: Features) -> Backend {
    Backend::select(f)
}

/// Why an AES-CBC operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key is not 16, 24 or 32 bytes long.
    InvalidKeyLength,
    /// The input length is not a multiple of 16 bytes.
    IncompleteBlock,
}

/// An expanded AES key for CBC encryption and decryption.
///
/// No padding is added or removed: each operation takes whole 16-byte
/// blocks. The chaining value is updated in place, so that a message may be
/// processed in pieces, each continuing from the last.
pub struct AesCbc {
    /// The key schedule `vg_aes_expand_key` writes.
    schedule: [u8; 240],
    /// The number of rounds of AES: 10, 12 or 14.
    rounds: usize,
    /// The implementation of AES the functions called use.
    backend: Backend,
}

impl AesCbc {
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

    /// Encrypts whole 16-byte blocks in place, chained from `iv`, and
    /// replaces `iv` with the last ciphertext block (leaving it unchanged
    /// for empty input), so that a further call continues the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 16.
    pub fn encrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) -> Result<(), Error> {
        let f = instance!(
            self.backend,
            vg_aes_cbc_encrypt,
            vg_aes_cbc_encrypt_aesni,
            vg_aes_cbc_encrypt_vaes,
            vg_aes_cbc_encrypt_aes
        );
        self.crypt(iv, buffer, f)
    }

    /// Decrypts whole 16-byte blocks in place, chained from `iv`, and
    /// replaces `iv` with the last ciphertext block (leaving it unchanged
    /// for empty input), so that a further call continues the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 16.
    pub fn decrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) -> Result<(), Error> {
        let f = instance!(
            self.backend,
            vg_aes_cbc_decrypt,
            vg_aes_cbc_decrypt_aesni,
            vg_aes_cbc_decrypt_vaes,
            vg_aes_cbc_decrypt_aes
        );
        self.crypt(iv, buffer, f)
    }

    fn crypt(&self, iv: &mut [u8; 16], buffer: &mut [u8], f: Cbc) -> Result<(), Error> {
        if !buffer.len().is_multiple_of(16) {
            return Err(Error::IncompleteBlock);
        }
        let mut scratch = [0; 272];
        // SAFETY: `rounds` is 10, 12 or 14 and the schedule holds its key
        // schedule; the buffer holds `len / 16` whole blocks, and it, the
        // chaining value, the schedule and the scratch space are separate
        // valid objects of the sizes of the signature. `select` chose `f` for
        // the CPU's features.
        unsafe {
            f(
                &self.schedule,
                self.rounds,
                iv,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 16,
                &mut scratch,
            );
        }
        // The scratch space may hold the key schedule, the data and our
        // caller's registers.
        zeroize(&mut scratch);
        Ok(())
    }
}

/// The signature of `vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt`.
#[cfg(target_arch = "x86_64")]
type Cbc = unsafe extern "sysv64" fn(
    *const [u8; 240],
    usize,
    *mut [u8; 16],
    *mut [u8; 16],
    usize,
    *mut [u64; 272],
);
/// The signature of `vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt`.
#[cfg(any(target_arch = "x86", target_arch = "aarch64", target_arch = "arm"))]
type Cbc = unsafe extern "C" fn(
    *const [u8; 240],
    usize,
    *mut [u8; 16],
    *mut [u8; 16],
    usize,
    *mut [u64; 272],
);

impl Drop for AesCbc {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}

#[cfg(test)]
mod tests {
    use super::{AesCbc, select};
    use crate::cpu::detected;

    /// A new key uses the implementation chosen for the CPU's features.
    #[test]
    fn select_detected() {
        for len in [16, 24, 32] {
            assert_eq!(
                AesCbc::new(&[0; 32][..len]).unwrap().backend,
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
