//! AES-OFB (SP 800-38A §6.4) with 128-, 192- and 256-bit keys, in place.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::aes::vg_aes_expand_key;
#[cfg(target_arch = "aarch64")]
use crate::arch::aes::vg_aes_expand_key_aes;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::aes::vg_aes_expand_key_aesni;
use crate::arch::aes_ofb::vg_aes_ofb;
#[cfg(target_arch = "aarch64")]
use crate::arch::aes_ofb::{VG_AES_OFB_AES_FEATURES, vg_aes_ofb_aes};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::aes_ofb::{VG_AES_OFB_AESNI_FEATURES, vg_aes_ofb_aesni};
#[cfg(target_arch = "x86_64")]
use crate::arch::aes_ofb::{VG_AES_OFB_VAES_FEATURES, vg_aes_ofb_vaes};
use crate::cipher::aes::Backend;
use crate::cpu::detected;
use crate::error::{IncompleteBlock, InvalidKeyLength};
use crate::zeroize::zeroize;
use verified_garbage_cpu::Features;

/// The variant of a function for `backend`: the baseline one, or its
/// `_aesni`, `_vaes` or `_aes` one.
macro_rules! instance {
    ($backend:expr, $scalar:ident, $aesni:ident, $vaes:ident, $aes:ident) => {
        match $backend {
            Backend::Scalar => $scalar,
            #[cfg(target_arch = "x86_64")]
            Backend::AesNi => $aesni,
            #[cfg(target_arch = "x86_64")]
            Backend::Vaes => $vaes,
            #[cfg(target_arch = "x86")]
            Backend::AesNi => $aesni,
            #[cfg(target_arch = "aarch64")]
            Backend::Aes => $aes,
        }
    };
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its OFB function.
#[cfg(target_arch = "x86_64")]
fn select(f: Features) -> Backend {
    Backend::select_for(f, VG_AES_OFB_VAES_FEATURES, VG_AES_OFB_AESNI_FEATURES)
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its OFB function.
#[cfg(target_arch = "x86")]
fn select(f: Features) -> Backend {
    Backend::select_for(f, VG_AES_OFB_AESNI_FEATURES)
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its OFB function.
#[cfg(target_arch = "aarch64")]
fn select(f: Features) -> Backend {
    Backend::select_for(f, VG_AES_OFB_AES_FEATURES)
}

/// The only implementation of AES on ARMv7, PPC64LE and RISC-V.
#[cfg(any(
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
fn select(f: Features) -> Backend {
    Backend::select(f)
}

/// An expanded AES key.
struct Key {
    /// The key schedule `vg_aes_expand_key` writes.
    schedule: [u8; 240],
    /// The number of rounds of AES: 10, 12 or 14.
    rounds: usize,
    /// The implementation of AES the function called uses.
    backend: Backend,
}

/// AES-OFB of one message, whose encryption and decryption are the
/// same operation.
///
/// Each call but the last takes whole 16-byte blocks and continues the
/// message from the last output block of the call before; the last,
/// [`apply_keystream_final`](Self::apply_keystream_final), takes the rest
/// of the message, of any length.
///
/// The IV must be unique to each message under a key (SP 800-38A Appendix C).
pub struct AesOfb {
    key: Key,
    /// The block to continue from: the IV, then the last output block.
    iv: [u8; 16],
}

impl AesOfb {
    /// Expands a 16-, 24- or 32-byte key, to process a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 16]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Encrypts or decrypts (the same operation) whole 16-byte blocks in
    /// place, continuing the message. Returns an error without changing
    /// anything if the buffer's length is not a multiple of 16: only
    /// [`apply_keystream_final`](Self::apply_keystream_final) takes a partial
    /// last block.
    pub fn apply_keystream(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(16) {
            return Err(IncompleteBlock);
        }
        self.key.apply_keystream(&mut self.iv, buffer);
        Ok(())
    }

    /// Encrypts or decrypts (the same operation) the rest of the message in
    /// place, of any length: its whole blocks, then a partial last block if
    /// there is one (§6.4, `Cₙ* = Pₙ* ⊕ MSB_u(Oₙ)`).
    pub fn apply_keystream_final(mut self, buffer: &mut [u8]) {
        self.key.apply_keystream(&mut self.iv, buffer);
    }
}

impl Drop for AesOfb {
    /// Wipes the block to continue from, an output block: keystream.
    fn drop(&mut self) {
        zeroize(&mut self.iv);
    }
}

impl Key {
    /// Expands a 16-, 24- or 32-byte key.
    fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(InvalidKeyLength);
        }
        let backend = select(detected());
        let expand = instance!(
            backend,
            vg_aes_expand_key,
            vg_aes_expand_key_aesni,
            vg_aes_expand_key_aesni,
            vg_aes_expand_key_aes
        );
        let mut schedule = [0; 240];
        // SAFETY: the key is 16, 24 or 32 bytes long; the key and the schedule
        // are separate valid buffers of the sizes of the signature, and
        // `select` chose `expand` for the CPU's features.
        unsafe { expand(key.as_ptr(), key.len(), &mut schedule) };
        Ok(Self {
            schedule,
            rounds: key.len() / 4 + 6,
            backend,
        })
    }

    /// Encrypts or decrypts (the same operation) `buffer` in place, from the
    /// block `iv`, which it replaces with the last output block used
    /// (unchanged for empty input). A message may be processed in pieces of
    /// whole blocks, each continuing from the `iv` the last left; a piece
    /// whose length is not a multiple of 16 bytes must end the message.
    fn apply_keystream(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        let whole = buffer.len() / 16 * 16;
        let (blocks, rest) = buffer.split_at_mut(whole);
        self.crypt(iv, blocks);
        if !rest.is_empty() {
            // The last bytes, padded to a block: OFB XORs them with the first
            // bytes of the next output block.
            let mut last = [0; 16];
            last[..rest.len()].copy_from_slice(rest);
            self.crypt(iv, &mut last);
            rest.copy_from_slice(&last[..rest.len()]);
            zeroize(&mut last);
        }
    }

    /// OFB of whole blocks.
    fn crypt(&self, iv: &mut [u8; 16], blocks: &mut [u8]) {
        let f = instance!(
            self.backend,
            vg_aes_ofb,
            vg_aes_ofb_aesni,
            vg_aes_ofb_vaes,
            vg_aes_ofb_aes
        );
        let mut scratch = [0; 272];
        // SAFETY: `rounds` is 10, 12 or 14 and the schedule holds its key
        // schedule; `blocks` holds `len / 16` whole blocks (its length is a
        // multiple of 16), and it, the block at `iv`, the schedule and the
        // scratch space are separate valid objects of the sizes of the
        // signature. `select` chose `f` for the CPU's features.
        unsafe {
            f(
                &self.schedule,
                self.rounds,
                iv,
                blocks.as_mut_ptr().cast(),
                blocks.len() / 16,
                &mut scratch,
            );
        }
        // The scratch space may hold the key schedule, the data and our
        // caller's registers.
        zeroize(&mut scratch);
    }
}

impl Drop for Key {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}

#[cfg(test)]
mod tests {
    use super::{Key, select};
    use crate::cpu::detected;

    /// A new key uses the implementation chosen for the CPU's features.
    #[test]
    fn select_detected() {
        for len in [16, 24, 32] {
            assert_eq!(
                Key::new(&[0; 32][..len]).unwrap().backend,
                select(detected())
            );
        }
    }

    /// Each implementation is chosen for the features of its function.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64"))]
    #[test]
    fn select_features() {
        use crate::cipher::aes::Backend;
        use verified_garbage_cpu::{Features, feature};
        assert_eq!(select(Features(0)), Backend::Scalar);
        #[cfg(target_arch = "x86_64")]
        {
            assert_eq!(
                select(Features(feature::AES | feature::SSSE3)),
                Backend::AesNi
            );
            let vaes = Features(
                feature::AES | feature::AVX | feature::AVX2 | feature::SSSE3 | feature::VAES,
            );
            assert_eq!(select(vaes), Backend::Vaes);
        }
        #[cfg(target_arch = "x86")]
        assert_eq!(select(Features(feature::AES)), Backend::AesNi);
        #[cfg(target_arch = "aarch64")]
        assert_eq!(select(Features(feature::AES)), Backend::Aes);
    }
}
