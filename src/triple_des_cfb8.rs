//! Triple DES-CFB8 (SP 800-38A §6.3 with 8-bit segments, with Triple DES as
//! in FIPS 46-3), in place.
//!
//! The block cipher work and the feedback are verified assembly:
//! `vg_triple_des_expand_key` (contract `VG.Spec.TripleDes.expandKeyContract`)
//! writes the key schedule, and `vg_triple_des_cfb8_encrypt` and
//! `vg_triple_des_cfb8_decrypt` (`VG.Spec.TripleDes.cfb8EncryptContract`,
//! `cfb8DecryptContract`) replace each byte with its XOR with the first byte
//! of `CIPH_K` of the input block, and the input block at `iv` with the one
//! to continue from, in constant time: their timing depends on none of the
//! key, the input block and the data. Both are the modes' generic CFB8 over
//! the scalar block function. This module holds the key schedule.

#![cfg(target_arch = "x86_64")]

use crate::arch::triple_des::vg_triple_des_expand_key;
use crate::arch::triple_des_cfb8::{vg_triple_des_cfb8_decrypt, vg_triple_des_cfb8_encrypt};
use crate::zeroize::zeroize;

/// The key does not contain 16 or 24 bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InvalidKeyLength;

/// An expanded Triple DES key for CFB8 encryption and decryption.
///
/// A 24-byte key encodes K1, K2 and K3. A 16-byte key encodes K1 and K2,
/// with K3 repeating K1. Each byte's parity bit is ignored.
pub struct TripleDesCfb8 {
    /// The key schedule `vg_triple_des_expand_key` writes.
    schedule: [u8; 384],
}

impl TripleDesCfb8 {
    /// Expands a 16- or 24-byte key for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 24) {
            return Err(InvalidKeyLength);
        }
        let mut schedule = [0; 384];
        // SAFETY: the key has a validated length; key and schedule are
        // separate valid buffers of the required sizes. The function zeroes
        // its working space on its own stack before returning.
        unsafe { vg_triple_des_expand_key(key.as_ptr(), key.len(), &mut schedule) };
        Ok(Self { schedule })
    }

    /// Encrypts `buffer` in place, from the input block `iv`, which it
    /// replaces with the one to continue from: its last `8 - n` bytes
    /// followed by the last `n` (up to 8) ciphertext bytes. A message may be
    /// encrypted in pieces of any length, each continuing from the `iv` the
    /// last left.
    pub fn encrypt(&self, iv: &mut [u8; 8], buffer: &mut [u8]) {
        // SAFETY: `buffer`, the block at `iv` and the schedule are separate
        // valid objects of the sizes of the signature, none of them on the
        // callee's stack. The function zeroes its working space on its own
        // stack before returning.
        unsafe {
            vg_triple_des_cfb8_encrypt(&self.schedule, iv, buffer.as_mut_ptr(), buffer.len())
        };
    }

    /// Decrypts `buffer` in place, from the input block `iv`, which it
    /// replaces with the one to continue from: its last `8 - n` bytes
    /// followed by the last `n` (up to 8) ciphertext bytes. A message may be
    /// decrypted in pieces of any length, each continuing from the `iv` the
    /// last left.
    pub fn decrypt(&self, iv: &mut [u8; 8], buffer: &mut [u8]) {
        // SAFETY: as in `encrypt`.
        unsafe {
            vg_triple_des_cfb8_decrypt(&self.schedule, iv, buffer.as_mut_ptr(), buffer.len())
        };
    }
}

impl Drop for TripleDesCfb8 {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
