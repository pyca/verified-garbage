//! Triple DES-CFB8 (SP 800-38A §6.3 with 8-bit segments, with Triple DES as in
//! FIPS 46-3), in place.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::align::CacheAligned;
use crate::arch::dispatch::triple_des::vg_triple_des_expand_key_auto;
use crate::arch::dispatch::triple_des_cfb8::{
    vg_triple_des_cfb8_decrypt_auto, vg_triple_des_cfb8_encrypt_auto,
};
use crate::error::InvalidKeyLength;
use crate::zeroize::zeroize;

/// An expanded Triple DES key, which serves both directions.
struct Key {
    /// The key schedule `vg_triple_des_expand_key` writes.
    schedule: CacheAligned<[u8; 384]>,
}

/// A Triple DES-CFB8 encryption of one message.
///
/// A message may be encrypted in pieces of any lengths, each continuing
/// where the last ended.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct TripleDesCfb8Encryptor {
    key: Key,
    /// The input block to continue from: the IV, then its last bytes
    /// followed by the ciphertext so far.
    iv: [u8; 8],
}

impl TripleDesCfb8Encryptor {
    /// Expands a 16- or 24-byte key (a 24-byte key encodes K1, K2 and K3; a
    /// 16-byte key, K1 and K2, with K3 repeating K1; each byte's parity bit is
    /// ignored), to encrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 8]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Encrypts `buffer` in place, continuing the message.
    pub fn encrypt(&mut self, buffer: &mut [u8]) {
        self.key.encrypt(&mut self.iv, buffer);
    }
}

/// A Triple DES-CFB8 decryption of one message.
///
/// A message may be decrypted in pieces of any lengths, each continuing
/// where the last ended.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct TripleDesCfb8Decryptor {
    key: Key,
    /// The input block to continue from: the IV, then its last bytes
    /// followed by the ciphertext so far.
    iv: [u8; 8],
}

impl TripleDesCfb8Decryptor {
    /// Expands a 16- or 24-byte key (a 24-byte key encodes K1, K2 and K3; a
    /// 16-byte key, K1 and K2, with K3 repeating K1; each byte's parity bit is
    /// ignored), to decrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 8]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Decrypts `buffer` in place, continuing the message.
    pub fn decrypt(&mut self, buffer: &mut [u8]) {
        self.key.decrypt(&mut self.iv, buffer);
    }
}

impl Key {
    /// Expands a 16- or 24-byte key.
    fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 24) {
            return Err(InvalidKeyLength);
        }
        let mut schedule = CacheAligned([0; 384]);
        crate::dit::enter!(dit);
        // SAFETY: the key has a validated length; key and schedule are separate
        // valid buffers of the required sizes.
        unsafe { vg_triple_des_expand_key_auto(dit, key.as_ptr(), key.len(), &mut schedule.0) };
        Ok(Self { schedule })
    }

    /// Encrypts `buffer` in place, from the input block `iv`, which it
    /// replaces with the one to continue from: its last `8 - n` bytes
    /// followed by the last `n` (up to 8) ciphertext bytes.
    fn encrypt(&self, iv: &mut [u8; 8], buffer: &mut [u8]) {
        crate::dit::enter!(dit);
        // SAFETY: `buffer`, the block at `iv` and the schedule are separate
        // valid objects of the sizes of the signature, none of them on the
        // callee's stack.
        unsafe {
            vg_triple_des_cfb8_encrypt_auto(
                dit,
                &self.schedule.0,
                iv,
                buffer.as_mut_ptr(),
                buffer.len(),
            )
        };
    }

    /// Decrypts `buffer` in place, from the input block `iv`, which it
    /// replaces with the one to continue from: its last `8 - n` bytes
    /// followed by the last `n` (up to 8) ciphertext bytes.
    fn decrypt(&self, iv: &mut [u8; 8], buffer: &mut [u8]) {
        crate::dit::enter!(dit);
        // SAFETY: as in `encrypt`.
        unsafe {
            vg_triple_des_cfb8_decrypt_auto(
                dit,
                &self.schedule.0,
                iv,
                buffer.as_mut_ptr(),
                buffer.len(),
            )
        };
    }
}

impl Drop for Key {
    fn drop(&mut self) {
        zeroize(&mut self.schedule.0);
    }
}
