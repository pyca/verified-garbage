//! AES-ECB (SP 800-38A §6.1) with 128-, 192- and 256-bit keys, in place and
//! without padding.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::align::CacheAligned;
use crate::arch::dispatch::aes::vg_aes_expand_key_auto;
use crate::arch::dispatch::aes_ecb::{vg_aes_ecb_decrypt_auto, vg_aes_ecb_encrypt_auto};
use crate::error::{IncompleteBlock, InvalidKeyLength};
use crate::zeroize::zeroize;
use core::mem::MaybeUninit;

/// An expanded AES key for ECB encryption and decryption.
///
/// No padding is added or removed: each operation takes whole 16-byte
/// blocks. ECB encrypts equal blocks to equal blocks, so it hides little
/// of the structure of the plaintext; it is offered for compatibility.
pub struct AesEcb {
    /// The key schedule `vg_aes_expand_key` writes.
    schedule: CacheAligned<[u8; 240]>,
    /// The number of rounds of AES: 10, 12 or 14.
    rounds: usize,
}

impl AesEcb {
    /// Expands a 16-, 24- or 32-byte key for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(InvalidKeyLength);
        }
        let mut schedule = CacheAligned([0; 240]);
        // SAFETY: the key is 16, 24 or 32 bytes long, and the key and the
        // schedule are separate valid buffers of the sizes of the signature.
        unsafe { vg_aes_expand_key_auto(key.as_ptr(), key.len(), &mut schedule.0) };
        Ok(Self {
            schedule,
            rounds: key.len() / 4 + 6,
        })
    }

    /// Encrypts whole 16-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is not a
    /// multiple of 16.
    pub fn encrypt(&self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        self.crypt(buffer, true)
    }

    /// Decrypts whole 16-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is not a
    /// multiple of 16.
    pub fn decrypt(&self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        self.crypt(buffer, false)
    }

    /// Encrypts (`encrypt`) or decrypts the blocks of `buffer` in place.
    fn crypt(&self, buffer: &mut [u8], encrypt: bool) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(16) {
            return Err(IncompleteBlock);
        }
        // The contracts hold whatever the working space holds, so it need
        // not be initialized; each function leaves each byte of it unchanged
        // or zero (`Spec.AesEcb`), so it need not be wiped.
        let mut scratch = CacheAligned(MaybeUninit::<[u64; 256]>::uninit());
        let data = buffer.as_mut_ptr().cast();
        let n = buffer.len() / 16;
        // SAFETY: `rounds` is 10, 12 or 14 and the schedule holds its key
        // schedule; the buffer holds `n` whole blocks, and it, the schedule
        // and the scratch space are separate valid objects of the sizes of
        // the signature.
        unsafe {
            if encrypt {
                vg_aes_ecb_encrypt_auto(
                    &self.schedule.0,
                    self.rounds,
                    data,
                    n,
                    scratch.0.as_mut_ptr(),
                );
            } else {
                vg_aes_ecb_decrypt_auto(
                    &self.schedule.0,
                    self.rounds,
                    data,
                    n,
                    scratch.0.as_mut_ptr(),
                );
            }
        }
        Ok(())
    }
}

impl Drop for AesEcb {
    fn drop(&mut self) {
        zeroize(&mut self.schedule.0);
    }
}
