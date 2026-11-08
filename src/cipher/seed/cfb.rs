//! SEED-CFB128 (SP 800-38A §6.3 with 128-bit segments, with SEED as in RFC
//! 4269), in place.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::align::CacheAligned;
use crate::arch::dispatch::seed::vg_seed_expand_key_auto;
use crate::arch::dispatch::seed_cfb::{
    vg_seed_cfb128_decrypt_auto, vg_seed_cfb128_decrypt_final_auto, vg_seed_cfb128_encrypt_auto,
    vg_seed_cfb128_encrypt_final_auto,
};
use crate::error::{IncompleteBlock, InvalidKeyLength};
use crate::zeroize::zeroize;

/// An expanded SEED key.
struct Key {
    /// The key schedule `vg_seed_expand_key` writes.
    schedule: CacheAligned<[u8; 128]>,
}

/// A SEED-CFB128 encryption of one message.
///
/// Each call but the last takes whole 16-byte blocks and continues the
/// message from the last ciphertext block of the call before; the last,
/// [`encrypt_final`](Self::encrypt_final), takes the rest of the message, of
/// any length.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct SeedCfb128Encryptor {
    key: Key,
    /// The block to continue from: the IV, then the last ciphertext block.
    iv: [u8; 16],
}

impl SeedCfb128Encryptor {
    /// Expands a 16-byte key, to encrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 16]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Encrypts whole 16-byte blocks in place, continuing the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 16: only [`encrypt_final`](Self::encrypt_final) takes
    /// a partial last segment.
    pub fn encrypt(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(16) {
            return Err(IncompleteBlock);
        }
        self.key.encrypt(&mut self.iv, buffer);
        Ok(())
    }

    /// Encrypts the rest of the message in place, of any length: its whole
    /// blocks, then a partial last segment if there is one,
    /// `Cₙ* = Pₙ* ⊕ MSB_u(CIPH_K(Cₙ₋₁))` (SP 800-38A defines CFB only for
    /// whole segments; this is the rule of its §6.4 and §6.5 for a partial
    /// last block, as other implementations extend CFB).
    pub fn encrypt_final(mut self, buffer: &mut [u8]) {
        self.key.last(
            &mut self.iv,
            buffer,
            vg_seed_cfb128_encrypt_auto,
            vg_seed_cfb128_encrypt_final_auto,
        );
    }
}

impl Drop for SeedCfb128Encryptor {
    /// Wipes the block to continue from, which after a partial last segment
    /// is keystream.
    fn drop(&mut self) {
        zeroize(&mut self.iv);
    }
}

/// A SEED-CFB128 decryption of one message.
///
/// Each call but the last takes whole 16-byte blocks and continues the
/// message from the last ciphertext block of the call before; the last,
/// [`decrypt_final`](Self::decrypt_final), takes the rest of the message, of
/// any length.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct SeedCfb128Decryptor {
    key: Key,
    /// The block to continue from: the IV, then the last ciphertext block.
    iv: [u8; 16],
}

impl SeedCfb128Decryptor {
    /// Expands a 16-byte key, to decrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 16]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Decrypts whole 16-byte blocks in place, continuing the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 16: only [`decrypt_final`](Self::decrypt_final) takes
    /// a partial last segment.
    pub fn decrypt(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(16) {
            return Err(IncompleteBlock);
        }
        self.key.decrypt(&mut self.iv, buffer);
        Ok(())
    }

    /// Decrypts the rest of the message in place, of any length: its whole
    /// blocks, then a partial last segment if there is one,
    /// `Pₙ* = Cₙ* ⊕ MSB_u(CIPH_K(Cₙ₋₁))` (SP 800-38A defines CFB only for
    /// whole segments; this is the rule of its §6.4 and §6.5 for a partial
    /// last block, as other implementations extend CFB).
    pub fn decrypt_final(mut self, buffer: &mut [u8]) {
        self.key.last(
            &mut self.iv,
            buffer,
            vg_seed_cfb128_decrypt_auto,
            vg_seed_cfb128_decrypt_final_auto,
        );
    }
}

impl Drop for SeedCfb128Decryptor {
    /// Wipes the block to continue from, which after a partial last segment
    /// is keystream.
    fn drop(&mut self) {
        zeroize(&mut self.iv);
    }
}

/// The signature of `vg_seed_cfb128_encrypt` and `vg_seed_cfb128_decrypt`.
#[cfg(target_arch = "x86_64")]
type Cfb = unsafe extern "sysv64" fn(*const [u8; 128], *mut [u8; 16], *mut [u8; 16], usize);
/// The signature of `vg_seed_cfb128_encrypt` and `vg_seed_cfb128_decrypt`.
#[cfg(any(
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
type Cfb = unsafe extern "C" fn(*const [u8; 128], *mut [u8; 16], *mut [u8; 16], usize);

/// The signature of `vg_seed_cfb128_encrypt_final` and `vg_seed_cfb128_decrypt_final`.
#[cfg(target_arch = "x86_64")]
type CfbFinal = unsafe extern "sysv64" fn(*const [u8; 128], *mut [u8; 16], *mut u8, usize);
/// The signature of `vg_seed_cfb128_encrypt_final` and `vg_seed_cfb128_decrypt_final`.
#[cfg(any(
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
type CfbFinal = unsafe extern "C" fn(*const [u8; 128], *mut [u8; 16], *mut u8, usize);

impl Key {
    /// Expands a 16-byte key.
    fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        let key: &[u8; 16] = key.try_into().map_err(|_| InvalidKeyLength)?;
        let mut schedule = CacheAligned([0; 128]);
        // SAFETY: key and schedule are separate valid buffers of the required
        // sizes.
        unsafe { vg_seed_expand_key_auto(key, &mut schedule.0) };
        Ok(Self { schedule })
    }

    /// Encrypts the whole blocks of `buffer` in place, from the block `iv`,
    /// which it replaces with the last ciphertext block (unchanged for empty
    /// input).
    fn encrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        self.blocks(iv, buffer, vg_seed_cfb128_encrypt_auto);
    }

    /// Decrypts the whole blocks of `buffer` in place, from the block `iv`,
    /// which it replaces with the last ciphertext block (unchanged for empty
    /// input).
    fn decrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        self.blocks(iv, buffer, vg_seed_cfb128_decrypt_auto);
    }

    /// `f` on whole blocks.
    fn blocks(&self, iv: &mut [u8; 16], blocks: &mut [u8], f: Cfb) {
        // SAFETY: `blocks` holds `len / 16` whole blocks (its length is a
        // multiple of 16), and it, the block at `iv` and the schedule are
        // separate valid objects of the sizes of the signature, none of them on
        // the callee's stack.
        unsafe {
            f(
                &self.schedule.0,
                iv,
                blocks.as_mut_ptr().cast(),
                blocks.len() / 16,
            )
        };
    }

    /// The rest of a message, of any length: its whole blocks with `whole`,
    /// the whole-block function (which, decrypting, may decrypt several at
    /// once), then the bytes after them, fewer than 16, with `f`, the final
    /// function of the same direction, from the IV the whole blocks leave.
    fn last(&self, iv: &mut [u8; 16], buffer: &mut [u8], whole: Cfb, f: CfbFinal) {
        let (blocks, rest) = buffer.split_at_mut(buffer.len() / 16 * 16);
        self.blocks(iv, blocks, whole);
        if !rest.is_empty() {
            self.final_(iv, rest, f);
        }
    }

    /// `f`, a final function, on the rest of a message, of any length: it
    /// replaces `iv` with the last ciphertext block, or, after a partial last
    /// segment, with keystream, which the caller wipes.
    fn final_(&self, iv: &mut [u8; 16], buffer: &mut [u8], f: CfbFinal) {
        // SAFETY: `buffer` is valid for `len` bytes, and it, the block
        // at `iv` and the schedule are separate valid objects of the sizes of
        // the signature, none of them on the callee's stack.
        unsafe { f(&self.schedule.0, iv, buffer.as_mut_ptr(), buffer.len()) };
    }
}

impl Drop for Key {
    fn drop(&mut self) {
        zeroize(&mut self.schedule.0);
    }
}
