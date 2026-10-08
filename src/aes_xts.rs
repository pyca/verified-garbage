//! XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) with 256-, 384- and
//! 512-bit keys (AES-128, AES-192 and AES-256), in place, with ciphertext
//! stealing for a data unit that is not of whole blocks.
//!
//! The blocks are verified assembly: `vg_aes_expand_key` (contract
//! `VG.Spec.Aes.expandKeyContract`) writes the key schedules of `Key1` and
//! `Key2`, `vg_aes_encrypt_blocks` (`encryptBlocksContract`) enciphers the
//! tweak value with `Key2`, and `vg_aes_xts_encrypt` and
//! `vg_aes_xts_decrypt` (`VG.Spec.Xts.aesEncryptContract`,
//! `aesDecryptContract`) replace whole blocks with their XTS encryption or
//! decryption with `Key1`, from a tweak they advance by `α` per block, in
//! constant time. This module checks the lengths, which the assembly does
//! not, and steals ciphertext (§5.3.2, §5.4.2) by moving bytes between the
//! last two blocks; every block is enciphered by the verified functions.
//!
//! On x86-64 and x86, CPUs with AES-NI run the `_aesni` functions
//! (`crate::aes::Backend`; there is no VAES implementation of whole blocks
//! yet, so its CPUs run them too); on AArch64, CPUs with the AES
//! instructions run the `_aes` ones. Elsewhere, and on other CPUs, the
//! constant-time bitsliced implementation runs.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use crate::aes::Backend;
#[cfg(target_arch = "aarch64")]
use crate::arch::aes::{
    VG_AES_ENCRYPT_BLOCKS_AES_FEATURES, vg_aes_encrypt_blocks_aes, vg_aes_expand_key_aes,
};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::aes::{
    VG_AES_ENCRYPT_BLOCKS_AESNI_FEATURES, vg_aes_encrypt_blocks_aesni, vg_aes_expand_key_aesni,
};
use crate::arch::aes::{vg_aes_encrypt_blocks, vg_aes_expand_key};
#[cfg(target_arch = "aarch64")]
use crate::arch::aes_xts::{
    VG_AES_XTS_DECRYPT_AES_FEATURES, VG_AES_XTS_ENCRYPT_AES_FEATURES, vg_aes_xts_decrypt_aes,
    vg_aes_xts_encrypt_aes,
};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::aes_xts::{
    VG_AES_XTS_DECRYPT_AESNI_FEATURES, VG_AES_XTS_ENCRYPT_AESNI_FEATURES, vg_aes_xts_decrypt_aesni,
    vg_aes_xts_encrypt_aesni,
};
use crate::arch::aes_xts::{vg_aes_xts_decrypt, vg_aes_xts_encrypt};
use crate::cpu::{Features, detected};
use crate::zeroize::zeroize;

/// The instance of a function for `backend`: the scalar one, x86-64's or
/// x86's for AES-NI, or AArch64's for the AES instructions.
macro_rules! instance {
    ($backend:expr, $scalar:ident, $aesni:ident, $aes:ident) => {
        match $backend {
            Backend::Scalar => $scalar,
            // No VAES implementation of XTS yet.
            #[cfg(target_arch = "x86_64")]
            Backend::AesNi | Backend::Vaes => $aesni,
            #[cfg(target_arch = "x86")]
            Backend::AesNi => $aesni,
            #[cfg(target_arch = "aarch64")]
            Backend::Aes => $aes,
        }
    };
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its XTS functions and its encryption of whole blocks.
#[cfg(target_arch = "x86_64")]
fn select(f: Features) -> Backend {
    const AESNI: Features = Features::all(&[
        VG_AES_XTS_ENCRYPT_AESNI_FEATURES,
        VG_AES_XTS_DECRYPT_AESNI_FEATURES,
        VG_AES_ENCRYPT_BLOCKS_AESNI_FEATURES,
    ]);
    Backend::select_for(f, AESNI, AESNI)
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its XTS functions and its encryption of whole blocks.
#[cfg(target_arch = "x86")]
fn select(f: Features) -> Backend {
    const AESNI: Features = Features::all(&[
        VG_AES_XTS_ENCRYPT_AESNI_FEATURES,
        VG_AES_XTS_DECRYPT_AESNI_FEATURES,
        VG_AES_ENCRYPT_BLOCKS_AESNI_FEATURES,
    ]);
    Backend::select_for(f, AESNI)
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its XTS functions and its encryption of whole blocks.
#[cfg(target_arch = "aarch64")]
fn select(f: Features) -> Backend {
    const AES: Features = Features::all(&[
        VG_AES_XTS_ENCRYPT_AES_FEATURES,
        VG_AES_XTS_DECRYPT_AES_FEATURES,
        VG_AES_ENCRYPT_BLOCKS_AES_FEATURES,
    ]);
    Backend::select_for(f, AES)
}

/// The only implementation of AES on ARMv7.
#[cfg(target_arch = "arm")]
fn select(f: Features) -> Backend {
    Backend::select(f)
}

/// The most blocks a data unit may have (IEEE Std 1619-2007 §5.1, NIST SP
/// 800-38E).
pub const MAX_BLOCKS: usize = 1 << 20;

/// Why an XTS-AES operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key is not 32, 48 or 64 bytes long.
    InvalidKeyLength,
    /// The two halves of the key, `Key1` and `Key2`, are equal, which
    /// SP 800-38E's implementation guidance (FIPS 140-3 IG C.I) forbids.
    EqualKeyHalves,
    /// The data unit is shorter than one block (16 bytes).
    DataUnitTooShort,
    /// The data unit is longer than [`MAX_BLOCKS`] blocks.
    DataUnitTooLong,
}

/// An XTS-AES key, `Key1 ‖ Key2`, expanded for encryption and decryption.
///
/// Each operation takes a whole data unit, of 16 bytes or more, and its
/// 16-byte tweak value `i` (for a storage device, usually the data unit's
/// number, little-endian).
pub struct AesXts {
    /// The key schedule of `Key1`, which enciphers the data.
    data_schedule: [u8; 240],
    /// The key schedule of `Key2`, which enciphers the tweak value.
    tweak_schedule: [u8; 240],
    /// The number of rounds of AES: 10, 12 or 14.
    rounds: usize,
    /// The implementation of AES the functions called use.
    backend: Backend,
}

/// The signature of `vg_aes_xts_encrypt` and `vg_aes_xts_decrypt`.
#[cfg(target_arch = "x86_64")]
type Xts = unsafe extern "sysv64" fn(
    *const [u8; 240],
    usize,
    *mut [u8; 16],
    *mut [u8; 16],
    usize,
    *mut [u64; 272],
);
/// The signature of `vg_aes_xts_encrypt` and `vg_aes_xts_decrypt`.
#[cfg(any(target_arch = "x86", target_arch = "aarch64", target_arch = "arm"))]
type Xts = unsafe extern "C" fn(
    *const [u8; 240],
    usize,
    *mut [u8; 16],
    *mut [u8; 16],
    usize,
    *mut [u64; 272],
);

impl AesXts {
    /// Expands a 32-, 48- or 64-byte key, `Key1 ‖ Key2`, for use in either
    /// direction.
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        if !matches!(key.len(), 32 | 48 | 64) {
            return Err(Error::InvalidKeyLength);
        }
        let (key1, key2) = key.split_at(key.len() / 2);
        // Without branching on the key's bytes, only on whether they are all
        // equal.
        if key1.iter().zip(key2).fold(0, |d, (a, b)| d | (a ^ b)) == 0 {
            return Err(Error::EqualKeyHalves);
        }
        let backend = select(detected());
        let expand = instance!(
            backend,
            vg_aes_expand_key,
            vg_aes_expand_key_aesni,
            vg_aes_expand_key_aes
        );
        let mut data_schedule = [0; 240];
        let mut tweak_schedule = [0; 240];
        // SAFETY: each half of the key is 16, 24 or 32 bytes long; it and
        // its schedule are separate valid buffers of the sizes of the
        // signature, and `select` chose `expand` for the CPU's features. The
        // function zeroes its working space on its own stack before
        // returning.
        unsafe {
            expand(key1.as_ptr(), key1.len(), &mut data_schedule);
            expand(key2.as_ptr(), key2.len(), &mut tweak_schedule);
        }
        Ok(Self {
            data_schedule,
            tweak_schedule,
            rounds: key1.len() / 4 + 6,
            backend,
        })
    }

    /// Encrypts the data unit `buffer` in place with the tweak value `i`
    /// (§5.3.2). Returns an error without changing the buffer if it is
    /// shorter than 16 bytes or longer than [`MAX_BLOCKS`] blocks.
    pub fn encrypt(&self, i: &[u8; 16], buffer: &mut [u8]) -> Result<(), Error> {
        let f = instance!(
            self.backend,
            vg_aes_xts_encrypt,
            vg_aes_xts_encrypt_aesni,
            vg_aes_xts_encrypt_aes
        );
        let mut tweak = self.tweak(i, buffer.len())?;
        let mut scratch = [0; 272];
        let (whole, tail) = buffer.split_at_mut(buffer.len() / 16 * 16);
        // Every whole block with its tweak; for a partial last block, the
        // last whole one is `CC`, and `tweak` is the next block's.
        self.blocks(f, &mut tweak, whole, &mut scratch);
        if !tail.is_empty() {
            // `Pₘ ‖ CP` with `Cₘ = MSB_b(CC)` behind it, enciphered with
            // the tweak of block `m`.
            let at = whole.len() - 16;
            let last = &mut whole[at..];
            last[..tail.len()].swap_with_slice(tail);
            self.blocks(f, &mut tweak, last, &mut scratch);
        }
        zeroize(&mut tweak);
        // The scratch space may hold the key schedule, the data and our
        // caller's registers.
        zeroize(&mut scratch);
        Ok(())
    }

    /// Decrypts the data unit `buffer` in place with the tweak value `i`
    /// (§5.4.2). Returns an error without changing the buffer if it is
    /// shorter than 16 bytes or longer than [`MAX_BLOCKS`] blocks.
    pub fn decrypt(&self, i: &[u8; 16], buffer: &mut [u8]) -> Result<(), Error> {
        let f = instance!(
            self.backend,
            vg_aes_xts_decrypt,
            vg_aes_xts_decrypt_aesni,
            vg_aes_xts_decrypt_aes
        );
        let mut tweak = self.tweak(i, buffer.len())?;
        let mut scratch = [0; 272];
        let (whole, tail) = buffer.split_at_mut(buffer.len() / 16 * 16);
        if tail.is_empty() {
            self.blocks(f, &mut tweak, whole, &mut scratch);
        } else {
            let (head, last) = whole.split_at_mut(whole.len() - 16);
            // The blocks before the last whole one; `tweak` is then that
            // one's, and the block after it, `m`, has the next.
            self.blocks(f, &mut tweak, head, &mut scratch);
            let mut next = tweak;
            let mut discard = [0; 16];
            self.blocks(f, &mut next, &mut discard, &mut scratch);
            zeroize(&mut discard);
            // `PP`, deciphered with the tweak of block `m`; then `Cₘ ‖ CP`
            // with `Pₘ = MSB_b(PP)` behind it, with the tweak of block
            // `m − 1`.
            self.blocks(f, &mut next, last, &mut scratch);
            last[..tail.len()].swap_with_slice(tail);
            self.blocks(f, &mut tweak, last, &mut scratch);
            zeroize(&mut next);
        }
        zeroize(&mut tweak);
        // The scratch space may hold the key schedule, the data and our
        // caller's registers.
        zeroize(&mut scratch);
        Ok(())
    }

    /// The first tweak, `T = AES-enc(Key2, i)`, after checking the length
    /// of the data unit.
    fn tweak(&self, i: &[u8; 16], len: usize) -> Result<[u8; 16], Error> {
        if len < 16 {
            return Err(Error::DataUnitTooShort);
        }
        if len > 16 * MAX_BLOCKS {
            return Err(Error::DataUnitTooLong);
        }
        let encrypt = instance!(
            self.backend,
            vg_aes_encrypt_blocks,
            vg_aes_encrypt_blocks_aesni,
            vg_aes_encrypt_blocks_aes
        );
        let mut tweak = *i;
        let mut scratch = [0; 256];
        // SAFETY: `rounds` is 10, 12 or 14 and the schedule holds its key
        // schedule; the tweak is one whole block, and it, the schedule and
        // the scratch space are separate valid objects of the sizes of the
        // signature. `select` chose `encrypt` for the CPU's features.
        unsafe {
            encrypt(
                &self.tweak_schedule,
                self.rounds,
                &mut tweak,
                1,
                &mut scratch,
            )
        };
        // The scratch space may hold the key schedule and the tweak.
        zeroize(&mut scratch);
        Ok(tweak)
    }

    /// Runs `f` on the whole blocks of `blocks`, from `tweak`, which it
    /// advances past them.
    fn blocks(&self, f: Xts, tweak: &mut [u8; 16], blocks: &mut [u8], scratch: &mut [u64; 272]) {
        // SAFETY: `rounds` is 10, 12 or 14 and the schedule holds its key
        // schedule; `blocks` holds `len / 16` whole blocks (its length is a
        // multiple of 16), and it, the tweak, the schedule and the scratch
        // space are separate valid objects of the sizes of the signature.
        // `select` chose `f` for the CPU's features.
        unsafe {
            f(
                &self.data_schedule,
                self.rounds,
                tweak,
                blocks.as_mut_ptr().cast(),
                blocks.len() / 16,
                scratch,
            );
        }
    }
}

impl Drop for AesXts {
    fn drop(&mut self) {
        zeroize(&mut self.data_schedule);
        zeroize(&mut self.tweak_schedule);
    }
}

#[cfg(test)]
mod tests {
    use super::{AesXts, select};
    use crate::cpu::detected;

    /// A new key uses the implementation chosen for the CPU's features.
    #[test]
    fn select_detected() {
        let key: [u8; 64] = core::array::from_fn(|i| i as u8);
        for len in [32, 48, 64] {
            assert_eq!(
                AesXts::new(&key[..len]).unwrap().backend,
                select(detected())
            );
        }
    }

    /// Each implementation is chosen for the features of its functions.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64"))]
    #[test]
    fn select_features() {
        use crate::aes::Backend;
        use crate::cpu::Features;
        assert_eq!(select(Features(0)), Backend::Scalar);
        #[cfg(target_arch = "x86_64")]
        {
            assert_eq!(select(Features::of(&["aes", "ssse3"])), Backend::AesNi);
            let vaes = Features::of(&["aes", "avx", "avx2", "ssse3", "vaes"]);
            assert_eq!(select(vaes), Backend::Vaes);
        }
        #[cfg(target_arch = "x86")]
        assert_eq!(select(Features::of(&["aes"])), Backend::AesNi);
        #[cfg(target_arch = "aarch64")]
        assert_eq!(select(Features::of(&["aes"])), Backend::Aes);
    }
}
