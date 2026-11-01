//! AES-ECB (SP 800-38A §6.1) with 128-, 192- and 256-bit keys, in place
//! and without padding.
//!
//! ECB is the block cipher applied to each block on its own, so the whole
//! mode is verified assembly: `vg_aes_expand_key` (contract
//! `VG.Spec.Aes.expandKeyContract`) writes the key schedule, and
//! `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`
//! (`encryptBlocksContract`, `decryptBlocksContract`) replace each block
//! with its `CIPHER` or `INVCIPHER`, in constant time. This module checks
//! the lengths, which the assembly does not, and holds the key schedule.
//!
//! The variants of these functions, with the same contracts, are chosen
//! with `crate::aes::Backend`, on CPUs with the features their `_FEATURES`
//! constants name (and the key expansion's): on x86-64, the `_vaes` ones,
//! then the `_aesni` ones (both with `vg_aes_expand_key_aesni`); on x86, the
//! `_aesni` ones; on AArch64, the `_aes` ones.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use core::mem::MaybeUninit;

use crate::aes::Backend;
#[cfg(target_arch = "aarch64")]
use crate::arch::aes::{
    VG_AES_DECRYPT_BLOCKS_AES_FEATURES, VG_AES_DECRYPT_BLOCKS_AES_SCRATCH_WRITTEN,
    VG_AES_ENCRYPT_BLOCKS_AES_FEATURES, VG_AES_ENCRYPT_BLOCKS_AES_SCRATCH_WRITTEN,
    vg_aes_decrypt_blocks_aes, vg_aes_encrypt_blocks_aes, vg_aes_expand_key_aes,
};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::aes::{
    VG_AES_DECRYPT_BLOCKS_AESNI_FEATURES, VG_AES_ENCRYPT_BLOCKS_AESNI_FEATURES,
    vg_aes_decrypt_blocks_aesni, vg_aes_encrypt_blocks_aesni, vg_aes_expand_key_aesni,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::aes::{
    VG_AES_DECRYPT_BLOCKS_VAES_FEATURES, VG_AES_ENCRYPT_BLOCKS_AESNI_SCRATCH_WRITTEN,
    VG_AES_ENCRYPT_BLOCKS_VAES_FEATURES, VG_AES_ENCRYPT_BLOCKS_VAES_SCRATCH_WRITTEN,
    vg_aes_decrypt_blocks_vaes, vg_aes_encrypt_blocks_vaes,
};
use crate::arch::aes::{vg_aes_decrypt_blocks, vg_aes_encrypt_blocks, vg_aes_expand_key};
use crate::cpu::detected;
use crate::zeroize::{zeroize, zeroize_raw};
use verified_garbage_cpu::Features;

/// The variant of a function for `backend`: the baseline one, or its
/// `_aesni`, `_vaes` or `_aes` one.
macro_rules! instance {
    ($backend:expr, $scalar:expr, $aesni:expr, $vaes:expr, $aes:expr) => {
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
/// its functions for whole blocks.
#[cfg(target_arch = "x86_64")]
fn select(f: Features) -> Backend {
    const AESNI: Features = Features::all(&[
        VG_AES_ENCRYPT_BLOCKS_AESNI_FEATURES,
        VG_AES_DECRYPT_BLOCKS_AESNI_FEATURES,
    ]);
    const VAES: Features = Features::all(&[
        VG_AES_ENCRYPT_BLOCKS_VAES_FEATURES,
        VG_AES_DECRYPT_BLOCKS_VAES_FEATURES,
    ]);
    Backend::select_for(f, VAES, AESNI)
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its functions for whole blocks.
#[cfg(target_arch = "x86")]
fn select(f: Features) -> Backend {
    const AESNI: Features = Features::all(&[
        VG_AES_ENCRYPT_BLOCKS_AESNI_FEATURES,
        VG_AES_DECRYPT_BLOCKS_AESNI_FEATURES,
    ]);
    Backend::select_for(f, AESNI)
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its functions for whole blocks.
#[cfg(target_arch = "aarch64")]
fn select(f: Features) -> Backend {
    const AES: Features = Features::all(&[
        VG_AES_ENCRYPT_BLOCKS_AES_FEATURES,
        VG_AES_DECRYPT_BLOCKS_AES_FEATURES,
    ]);
    Backend::select_for(f, AES)
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

/// Why an AES-ECB operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key is not 16, 24 or 32 bytes long.
    InvalidKeyLength,
    /// The input length is not a multiple of 16 bytes.
    IncompleteBlock,
}

crate::error::impl_error! {
    Error {
        InvalidKeyLength => "invalid AES key length",
        IncompleteBlock => "AES-ECB input is not a whole number of blocks",
    }
}

/// An expanded AES key for ECB encryption and decryption.
///
/// No padding is added or removed: each operation takes whole 16-byte
/// blocks. ECB encrypts equal blocks to equal blocks, so it hides little
/// of the structure of the plaintext; it is offered for compatibility.
pub struct AesEcb {
    /// The key schedule `vg_aes_expand_key` writes.
    schedule: [u8; 240],
    /// The number of rounds of AES: 10, 12 or 14.
    rounds: usize,
    /// The implementation of AES the functions called are.
    backend: Backend,
}

impl AesEcb {
    /// Expands a 16-, 24- or 32-byte key for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(Error::InvalidKeyLength);
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

    /// Encrypts whole 16-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is not a
    /// multiple of 16.
    pub fn encrypt(&self, buffer: &mut [u8]) -> Result<(), Error> {
        let f = instance!(
            self.backend,
            vg_aes_encrypt_blocks,
            vg_aes_encrypt_blocks_aesni,
            vg_aes_encrypt_blocks_vaes,
            vg_aes_encrypt_blocks_aes
        );
        let written = instance!(
            self.backend,
            SCRATCH,
            ENCRYPT_AESNI_WRITTEN,
            VG_AES_ENCRYPT_BLOCKS_VAES_SCRATCH_WRITTEN,
            VG_AES_ENCRYPT_BLOCKS_AES_SCRATCH_WRITTEN
        );
        self.crypt(buffer, f, written)
    }

    /// Decrypts whole 16-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is not a
    /// multiple of 16.
    pub fn decrypt(&self, buffer: &mut [u8]) -> Result<(), Error> {
        let f = instance!(
            self.backend,
            vg_aes_decrypt_blocks,
            vg_aes_decrypt_blocks_aesni,
            vg_aes_decrypt_blocks_vaes,
            vg_aes_decrypt_blocks_aes
        );
        let written = instance!(
            self.backend,
            SCRATCH,
            SCRATCH,
            SCRATCH,
            VG_AES_DECRYPT_BLOCKS_AES_SCRATCH_WRITTEN
        );
        self.crypt(buffer, f, written)
    }

    /// Applies `f`, which writes at most the first `written` bytes of its
    /// working space, to the blocks of `buffer`.
    fn crypt(&self, buffer: &mut [u8], f: Blocks, written: usize) -> Result<(), Error> {
        if !buffer.len().is_multiple_of(16) {
            return Err(Error::IncompleteBlock);
        }
        // The contracts hold whatever the working space holds, so it need
        // not be initialized.
        let mut scratch = MaybeUninit::<[u64; 256]>::uninit();
        // SAFETY: `rounds` is 10, 12 or 14 and the schedule holds its key
        // schedule; the buffer holds `len / 16` whole blocks, and it, the
        // schedule and the scratch space are separate valid objects of the
        // sizes of the signature. `select` chose `f` for the CPU's features.
        unsafe {
            f(
                &self.schedule,
                self.rounds,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 16,
                scratch.as_mut_ptr(),
            );
        }
        // The scratch space may hold the key schedule and the data, in the
        // bytes the function writes (`Artifact.written`).
        // SAFETY: `written` is at most the 2048 bytes of `scratch`, a distinct
        // object, valid for writes.
        unsafe { zeroize_raw(scratch.as_mut_ptr().cast::<u8>(), written) };
        Ok(())
    }
}

/// The size of the working space of `vg_aes_encrypt_blocks` and
/// `vg_aes_decrypt_blocks`, in bytes: the bytes a function without a smaller
/// `Artifact.written` may write.
const SCRATCH: usize = size_of::<[u64; 256]>();

/// The bytes of the working space `vg_aes_encrypt_blocks_aesni` writes: none
/// on x86-64 (`VG_AES_ENCRYPT_BLOCKS_AESNI_SCRATCH_WRITTEN`); on x86, which
/// states no smaller bound, all of them.
#[cfg(target_arch = "x86_64")]
const ENCRYPT_AESNI_WRITTEN: usize = VG_AES_ENCRYPT_BLOCKS_AESNI_SCRATCH_WRITTEN;
#[cfg(target_arch = "x86")]
const ENCRYPT_AESNI_WRITTEN: usize = SCRATCH;

/// The signature of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`.
#[cfg(target_arch = "x86_64")]
type Blocks =
    unsafe extern "sysv64" fn(*const [u8; 240], usize, *mut [u8; 16], usize, *mut [u64; 256]);
/// The signature of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`.
#[cfg(any(
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "powerpc64",
    target_arch = "riscv64"
))]
type Blocks = unsafe extern "C" fn(*const [u8; 240], usize, *mut [u8; 16], usize, *mut [u64; 256]);

impl Drop for AesEcb {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}

#[cfg(test)]
mod tests {
    use super::{AesEcb, select};
    use crate::cpu::detected;

    /// A new key uses the implementation chosen for the CPU's features.
    #[test]
    fn select_detected() {
        for len in [16, 24, 32] {
            assert_eq!(
                AesEcb::new(&[0; 32][..len]).unwrap().backend,
                select(detected())
            );
        }
    }

    /// Each implementation is chosen for the features of its functions.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64"))]
    #[test]
    fn select_features() {
        use crate::aes::Backend;
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
