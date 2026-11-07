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

use crate::arch::dispatch::aes::{
    vg_aes_decrypt_blocks_auto, vg_aes_encrypt_blocks_auto, vg_aes_expand_key_auto,
};
use crate::error::{IncompleteBlock, InvalidKeyLength};
use crate::zeroize::{zeroize, zeroize_raw};
use core::mem::MaybeUninit;

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
}

impl AesEcb {
    /// Expands a 16-, 24- or 32-byte key for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(InvalidKeyLength);
        }
        let mut schedule = [0; 240];
        // SAFETY: the key is 16, 24 or 32 bytes long; the key and the schedule
        // are separate valid buffers of the sizes of the signature. The
        // dispatcher calls only an implementation the CPU has the features of.
        unsafe { vg_aes_expand_key_auto(key.as_ptr(), key.len(), &mut schedule) };
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
        // not be initialized.
        let mut scratch = MaybeUninit::<[u64; 256]>::uninit();
        let (data, n) = (buffer.as_mut_ptr().cast(), buffer.len() / 16);
        // SAFETY: `rounds` is 10, 12 or 14 and the schedule holds its key
        // schedule; the buffer holds `len / 16` whole blocks, and it, the
        // schedule and the scratch space are separate valid objects of the
        // sizes of the signature. The dispatcher calls only an implementation
        // the CPU has the features of.
        unsafe {
            if encrypt {
                vg_aes_encrypt_blocks_auto(
                    &self.schedule,
                    self.rounds,
                    data,
                    n,
                    scratch.as_mut_ptr(),
                );
            } else {
                vg_aes_decrypt_blocks_auto(
                    &self.schedule,
                    self.rounds,
                    data,
                    n,
                    scratch.as_mut_ptr(),
                );
            }
        }
        // The scratch space may hold the key schedule and the data. Not every
        // implementation the dispatcher may call bounds the bytes it writes
        // (`Artifact.written`), so all of them are wiped.
        // SAFETY: `scratch` is a distinct object, valid for writes of its
        // `size_of::<[u64; 256]>()` bytes.
        unsafe { zeroize_raw(scratch.as_mut_ptr().cast::<u8>(), size_of::<[u64; 256]>()) };
        Ok(())
    }
}

impl Drop for AesEcb {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
