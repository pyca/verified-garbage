//! Camellia-CFB128 (SP 800-38A §6.3 with 128-bit segments, with Camellia as in
//! RFC 3713) with 128-, 192- and 256-bit keys, in place.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::camellia::vg_camellia_expand_key;
use crate::arch::camellia_cfb::{
    vg_camellia_cfb128_decrypt, vg_camellia_cfb128_decrypt_final, vg_camellia_cfb128_encrypt,
    vg_camellia_cfb128_encrypt_final,
};
use crate::error::{IncompleteBlock, InvalidKeyLength};
use crate::zeroize::zeroize;

/// An expanded Camellia key.
struct Key {
    /// The subkeys `vg_camellia_expand_key` writes.
    schedule: [u8; 272],
    /// The number of rounds: 18 or 24.
    rounds: usize,
}

/// A Camellia-CFB128 encryption of one message.
///
/// Each call but the last takes whole 16-byte blocks and continues the
/// message from the last ciphertext block of the call before; the last,
/// [`encrypt_final`](Self::encrypt_final), takes the rest of the message, of
/// any length.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct CamelliaCfb128Encryptor {
    key: Key,
    /// The block to continue from: the IV, then the last ciphertext block.
    iv: [u8; 16],
}

impl CamelliaCfb128Encryptor {
    /// Expands a 16-, 24- or 32-byte key (16-byte keys use 18 rounds; 24- and
    /// 32-byte keys, 24), to encrypt a message from `iv`.
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
            vg_camellia_cfb128_encrypt,
            vg_camellia_cfb128_encrypt_final,
        );
    }
}

impl Drop for CamelliaCfb128Encryptor {
    /// Wipes the block to continue from, which after a partial last segment
    /// is keystream.
    fn drop(&mut self) {
        zeroize(&mut self.iv);
    }
}

/// A Camellia-CFB128 decryption of one message.
///
/// Each call but the last takes whole 16-byte blocks and continues the
/// message from the last ciphertext block of the call before; the last,
/// [`decrypt_final`](Self::decrypt_final), takes the rest of the message, of
/// any length.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct CamelliaCfb128Decryptor {
    key: Key,
    /// The block to continue from: the IV, then the last ciphertext block.
    iv: [u8; 16],
}

impl CamelliaCfb128Decryptor {
    /// Expands a 16-, 24- or 32-byte key (16-byte keys use 18 rounds; 24- and
    /// 32-byte keys, 24), to decrypt a message from `iv`.
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
            vg_camellia_cfb128_decrypt,
            vg_camellia_cfb128_decrypt_final,
        );
    }
}

impl Drop for CamelliaCfb128Decryptor {
    /// Wipes the block to continue from, which after a partial last segment
    /// is keystream.
    fn drop(&mut self) {
        zeroize(&mut self.iv);
    }
}

/// The signature of `vg_camellia_cfb128_encrypt` and `vg_camellia_cfb128_decrypt`.
#[cfg(target_arch = "x86_64")]
type Cfb = unsafe extern "sysv64" fn(*const [u8; 272], usize, *mut [u8; 16], *mut [u8; 16], usize);
/// The signature of `vg_camellia_cfb128_encrypt` and `vg_camellia_cfb128_decrypt`.
#[cfg(any(
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
type Cfb = unsafe extern "C" fn(*const [u8; 272], usize, *mut [u8; 16], *mut [u8; 16], usize);

/// The signature of `vg_camellia_cfb128_encrypt_final` and `vg_camellia_cfb128_decrypt_final`.
#[cfg(target_arch = "x86_64")]
type CfbFinal = unsafe extern "sysv64" fn(*const [u8; 272], usize, *mut [u8; 16], *mut u8, usize);
/// The signature of `vg_camellia_cfb128_encrypt_final` and `vg_camellia_cfb128_decrypt_final`.
#[cfg(any(
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
type CfbFinal = unsafe extern "C" fn(*const [u8; 272], usize, *mut [u8; 16], *mut u8, usize);

impl Key {
    /// Expands a 16-, 24- or 32-byte key.
    fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        let rounds = match key.len() {
            16 => 18,
            24 | 32 => 24,
            _ => return Err(InvalidKeyLength),
        };
        let mut schedule = [0; 272];
        // SAFETY: the key has a validated length; key and schedule are separate
        // valid buffers of the required sizes.
        unsafe { vg_camellia_expand_key(key.as_ptr(), key.len(), &mut schedule) };
        Ok(Self { schedule, rounds })
    }

    /// Encrypts the whole blocks of `buffer` in place, from the block `iv`,
    /// which it replaces with the last ciphertext block (unchanged for empty
    /// input).
    fn encrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        self.blocks(iv, buffer, vg_camellia_cfb128_encrypt);
    }

    /// Decrypts the whole blocks of `buffer` in place, from the block `iv`,
    /// which it replaces with the last ciphertext block (unchanged for empty
    /// input).
    fn decrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        self.blocks(iv, buffer, vg_camellia_cfb128_decrypt);
    }

    /// `f` on whole blocks.
    fn blocks(&self, iv: &mut [u8; 16], blocks: &mut [u8], f: Cfb) {
        // SAFETY: `rounds` is 18 or 24 and the schedule holds that many rounds'
        // subkeys; `blocks` holds `len / 16` whole blocks (its length is a
        // multiple of 16), and it, the block at `iv` and the schedule are
        // separate valid objects of the sizes of the signature, none of them on
        // the callee's stack.
        unsafe {
            f(
                &self.schedule,
                self.rounds,
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
        // SAFETY: `rounds` is a number of rounds the schedule holds subkeys for; `buffer` is valid for `len` bytes, and it, the block
        // at `iv` and the schedule are separate valid objects of the sizes of
        // the signature, none of them on the callee's stack.
        unsafe {
            f(
                &self.schedule,
                self.rounds,
                iv,
                buffer.as_mut_ptr(),
                buffer.len(),
            )
        };
    }
}

impl Drop for Key {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
