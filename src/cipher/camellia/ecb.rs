//! Camellia-ECB (RFC 3713), in place and without padding.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::camellia::{
    vg_camellia_ecb_decrypt, vg_camellia_ecb_encrypt, vg_camellia_expand_key,
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
    schedule: [u8; 272],
    rounds: usize,
}

impl CamelliaEcb {
    /// Expands a 16-, 24- or 32-byte key for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        crate::dit::enter!(dit);
        let rounds = match key.len() {
            16 => 18,
            24 | 32 => 24,
            _ => return Err(InvalidKeyLength),
        };
        let mut schedule = [0; 272];
        // SAFETY: the key has a validated length; key and schedule are separate
        // valid buffers of the required sizes.
        unsafe {
            vg_camellia_expand_key(dit, key.as_ptr(), key.len(), &mut schedule);
        }
        Ok(Self { schedule, rounds })
    }

    /// Encrypts complete 16-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn encrypt(&self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        crate::dit::enter!(dit);
        self.crypt(dit, buffer, true)
    }

    /// Decrypts complete 16-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn decrypt(&self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        crate::dit::enter!(dit);
        self.crypt(dit, buffer, false)
    }

    fn crypt(
        &self,
        dit: crate::dit::Dit<'_>,
        buffer: &mut [u8],
        encrypt: bool,
    ) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(16) {
            return Err(IncompleteBlock);
        }
        let f = if encrypt {
            vg_camellia_ecb_encrypt
        } else {
            vg_camellia_ecb_decrypt
        };
        // SAFETY: `rounds` is 18 for a key of 16 bytes and 24 otherwise, as
        // `new` expanded the schedule for. The buffer contains complete 16-byte
        // blocks, including zero blocks. The buffer and schedule are separate
        // valid objects and do not overlap the callee's stack.
        unsafe {
            f(
                dit,
                &self.schedule,
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
        zeroize(&mut self.schedule);
    }
}
