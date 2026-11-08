//! Camellia-ECB (RFC 3713), in place and without padding.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::align::CacheAligned;
use crate::arch::dispatch::camellia::{
    vg_camellia_ecb_decrypt_auto, vg_camellia_ecb_encrypt_auto, vg_camellia_expand_key_auto,
};
use crate::error::{IncompleteBlock, InvalidKeyLength};
use crate::zeroize::zeroize;

/// An expanded Camellia key for ECB encryption and decryption.
///
/// Keys of 16 bytes use 18 rounds; keys of 24 or 32 bytes, 24. No padding
/// is added or removed.
///
/// ECB encrypts equal blocks to equal blocks, so it reveals patterns in the
/// data.
pub struct CamelliaEcb {
    schedule: CacheAligned<[u8; 272]>,
    rounds: usize,
}

impl CamelliaEcb {
    /// Expands a 16-, 24- or 32-byte key for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        let rounds = match key.len() {
            16 => 18,
            24 | 32 => 24,
            _ => return Err(InvalidKeyLength),
        };
        let mut schedule = CacheAligned([0; 272]);
        // SAFETY: the key has a validated length; key and schedule are separate
        // valid buffers of the required sizes.
        unsafe {
            vg_camellia_expand_key_auto(key.as_ptr(), key.len(), &mut schedule.0);
        }
        Ok(Self { schedule, rounds })
    }

    /// Encrypts complete 16-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn encrypt(&self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        self.crypt(buffer, true)
    }

    /// Decrypts complete 16-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn decrypt(&self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        self.crypt(buffer, false)
    }

    fn crypt(&self, buffer: &mut [u8], encrypt: bool) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(16) {
            return Err(IncompleteBlock);
        }
        let f = if encrypt {
            vg_camellia_ecb_encrypt_auto
        } else {
            vg_camellia_ecb_decrypt_auto
        };
        // SAFETY: `rounds` is 18 for a key of 16 bytes and 24 otherwise, as
        // `new` expanded the schedule for. The buffer contains complete 16-byte
        // blocks, including zero blocks. The buffer and schedule are separate
        // valid objects and do not overlap the callee's stack.
        unsafe {
            f(
                &self.schedule.0,
                self.rounds,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 16,
            );
        }
        Ok(())
    }
}

impl Drop for CamelliaEcb {
    fn drop(&mut self) {
        zeroize(&mut self.schedule.0);
    }
}
