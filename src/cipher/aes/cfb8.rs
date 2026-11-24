//! AES-CFB8 (SP 800-38A §6.3, with 8-bit segments) with 128-, 192- and 256-bit
//! keys, in place.

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
use crate::arch::dispatch::aes_cfb8::{vg_aes_cfb8_decrypt_auto, vg_aes_cfb8_encrypt_auto};
use crate::error::InvalidKeyLength;
use crate::zeroize::zeroize;

/// An expanded AES key, which serves both directions.
struct Key {
    /// The key schedule `vg_aes_expand_key` writes.
    schedule: CacheAligned<[u8; 240]>,
    /// The number of rounds of AES: 10, 12 or 14.
    rounds: usize,
}

/// An AES-CFB8 encryption of one message.
///
/// A message may be encrypted in pieces of any lengths, each continuing
/// where the last ended.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct AesCfb8Encryptor {
    key: Key,
    /// The input block to continue from: the IV, then its last bytes
    /// followed by the ciphertext so far.
    iv: [u8; 16],
}

impl AesCfb8Encryptor {
    /// Expands a 16-, 24- or 32-byte key, to encrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 16]) -> Result<Self, InvalidKeyLength> {
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

/// An AES-CFB8 decryption of one message.
///
/// A message may be decrypted in pieces of any lengths, each continuing
/// where the last ended.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct AesCfb8Decryptor {
    key: Key,
    /// The input block to continue from: the IV, then its last bytes
    /// followed by the ciphertext so far.
    iv: [u8; 16],
}

impl AesCfb8Decryptor {
    /// Expands a 16-, 24- or 32-byte key, to decrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 16]) -> Result<Self, InvalidKeyLength> {
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
    /// Expands a 16-, 24- or 32-byte key.
    fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(InvalidKeyLength);
        }
        crate::dit::enter!(dit);
        let mut schedule = CacheAligned([0; 240]);
        // SAFETY: the key is 16, 24 or 32 bytes long; the key and the schedule
        // are separate valid buffers of the sizes of the signature. The
        // dispatcher calls only an implementation the CPU has the features of.
        unsafe { vg_aes_expand_key_auto(dit, key.as_ptr(), key.len(), &mut schedule.0) };
        Ok(Self {
            schedule,
            rounds: key.len() / 4 + 6,
        })
    }

    /// Encrypts `buffer` in place, from the input block `iv`, which it
    /// replaces with the one to continue from: its last `16 - n` bytes
    /// followed by the last `n` (up to 16) ciphertext bytes.
    fn encrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        self.crypt(iv, buffer, true);
    }

    /// Decrypts `buffer` in place, from the input block `iv`, which it
    /// replaces with the one to continue from: its last `16 - n` bytes
    /// followed by the last `n` (up to 16) ciphertext bytes.
    fn decrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        self.crypt(iv, buffer, false);
    }

    fn crypt(&self, iv: &mut [u8; 16], buffer: &mut [u8], encrypt: bool) {
        crate::dit::enter!(dit);
        let mut scratch = CacheAligned([0; 272]);
        // SAFETY: `rounds` is 10, 12 or 14 and the schedule holds its key
        // schedule; `buffer`, the block at `iv`, the schedule and the scratch
        // space are separate valid objects of the sizes of the signature. The
        // dispatcher calls only an implementation the CPU has the features of.
        unsafe {
            if encrypt {
                vg_aes_cfb8_encrypt_auto(
                    dit,
                    &self.schedule.0,
                    self.rounds,
                    iv,
                    buffer.as_mut_ptr(),
                    buffer.len(),
                    &mut scratch.0,
                );
            } else {
                vg_aes_cfb8_decrypt_auto(
                    dit,
                    &self.schedule.0,
                    self.rounds,
                    iv,
                    buffer.as_mut_ptr(),
                    buffer.len(),
                    &mut scratch.0,
                );
            }
        }
        // The scratch space may hold the key schedule, the data and our
        // caller's registers.
        zeroize(&mut scratch.0);
    }
}

impl Drop for Key {
    fn drop(&mut self) {
        zeroize(&mut self.schedule.0);
    }
}

#[cfg(test)]
mod tests {
    use super::{AesCfb8Decryptor, AesCfb8Encryptor};

    /// The longest message: more than three groups of the bytes an
    /// implementation may take at a time.
    const MAX: usize = 200;

    /// Decryption undoes encryption for messages of many bytes, which an
    /// implementation may take many at a time, split around any of the byte
    /// counts it may change its course at, and unaligned.
    #[test]
    fn byte_batches_and_continuation() {
        let iv = [0x3c; 16];
        let key: [u8; 32] = core::array::from_fn(|i| (17 * i + 3) as u8);
        let plain: [u8; MAX] = core::array::from_fn(|i| (73 * i + 5) as u8);
        for key in [&key[..16], &key[..24], &key[..]] {
            for len in [0usize, 1, 15, 16, 17, 63, 64, 65, 127, 128, 129, MAX] {
                let mut ciphertext = plain;
                AesCfb8Encryptor::new(key, &iv)
                    .unwrap()
                    .encrypt(&mut ciphertext[..len]);
                for split in [0, len.min(1), len / 2, len] {
                    let mut guarded = [0xa5; MAX + 2];
                    guarded[1..=len].copy_from_slice(&ciphertext[..len]);
                    let mut decryptor = AesCfb8Decryptor::new(key, &iv).unwrap();
                    let (first, rest) = guarded[1..=len].split_at_mut(split);
                    decryptor.decrypt(first);
                    decryptor.decrypt(rest);
                    assert_eq!(guarded[1..=len], plain[..len]);
                    assert_eq!((guarded[0], guarded[len + 1]), (0xa5, 0xa5));
                }
            }
        }
    }
}
