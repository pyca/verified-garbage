//! Triple DES-ECB (FIPS 46-3), in place and without padding.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::align::CacheAligned;
use crate::arch::dispatch::triple_des::{
    vg_triple_des_ecb_decrypt_auto, vg_triple_des_ecb_encrypt_auto,
};
use crate::arch::triple_des::vg_triple_des_expand_key;
use crate::error::{IncompleteBlock, InvalidKeyLength};
use crate::zeroize::zeroize;

/// An expanded Triple DES key for ECB encryption and decryption.
///
/// A 24-byte key encodes K1, K2 and K3. A 16-byte key encodes K1 and K2,
/// with K3 repeating K1. Each byte's parity bit is ignored; weak and
/// repeated component keys are accepted. No padding is added or removed.
///
/// ECB encrypts equal blocks to equal blocks, so it reveals patterns in the
/// data.
pub struct TripleDesEcb {
    schedule: CacheAligned<[u8; 384]>,
}

impl TripleDesEcb {
    /// Expands a 16- or 24-byte key for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 24) {
            return Err(InvalidKeyLength);
        }
        let mut schedule = CacheAligned([0; 384]);
        // SAFETY: the key has a validated length; key and schedule are separate
        // valid buffers of the required sizes.
        unsafe {
            vg_triple_des_expand_key(key.as_ptr(), key.len(), &mut schedule.0);
        }
        Ok(Self { schedule })
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
        let f = if encrypt {
            vg_triple_des_ecb_encrypt_auto
        } else {
            vg_triple_des_ecb_decrypt_auto
        };
        // SAFETY: buffer contains complete eight-byte blocks, including zero
        // blocks. The buffer and schedule are separate valid objects and do not
        // overlap the callee's stack. The dispatcher calls only an implementation
        // the CPU has the features of.
        unsafe {
            f(
                &self.schedule.0,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 8,
            );
        }
        Ok(())
    }
}

impl Drop for TripleDesEcb {
    fn drop(&mut self) {
        zeroize(&mut self.schedule.0);
    }
}
