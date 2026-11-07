//! AES-CCM (NIST SP 800-38C, with the formatting and counter generation of its
//! Appendix A, as RFC 3610) with 128-, 192- and 256-bit keys.
//!
//! A nonce must never be used twice with the same key. The tag length, 4, 6, 8,
//! 10, 12, 14 or 16 bytes (Appendix A.1), is a type parameter, `T` in
//! [`AesCcm::encrypt_in_place`] and [`AesCcm::decrypt_in_place`], so that it is
//! fixed in the caller's code and never taken from a message (see
//! `crate::aead::aes_gcm`).

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::aes::vg_aes_expand_key_auto;
use crate::arch::dispatch::aes_ccm::{vg_aes_ccm_open_auto, vg_aes_ccm_seal_auto};
use crate::error::InvalidKeyLength;
use crate::zeroize::zeroize;

// The `_aes_cbc` (AArch64) or `_aesni_cbc` (x86-64) implementations, which
// the dispatchers never choose: `seal` and `open` run them on long inputs
// (`cbc`), where they are faster.
#[cfg(target_arch = "aarch64")]
use crate::arch::aes_ccm::{
    VG_AES_CCM_OPEN_AES_CBC_FEATURES as OPEN_CBC_FEATURES,
    VG_AES_CCM_SEAL_AES_CBC_FEATURES as SEAL_CBC_FEATURES, vg_aes_ccm_open_aes_cbc as open_cbc,
    vg_aes_ccm_seal_aes_cbc as seal_cbc,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::aes_ccm::{
    VG_AES_CCM_OPEN_AESNI_CBC_FEATURES as OPEN_CBC_FEATURES,
    VG_AES_CCM_SEAL_AESNI_CBC_FEATURES as SEAL_CBC_FEATURES, vg_aes_ccm_open_aesni_cbc as open_cbc,
    vg_aes_ccm_seal_aesni_cbc as seal_cbc,
};
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
use crate::cpu::detected;

/// Whether to run the `_aes_cbc` instances (on AArch64) or the
/// `_aesni_cbc` ones (on x86-64), for `aad_len` bytes of associated data and
/// `len` bytes of payload: when they are longer than 32 bytes together (as
/// `crate::cmac::aes` chooses for an update), where those are faster.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
fn cbc(aad_len: usize, len: usize) -> bool {
    aad_len.saturating_add(len) > 32
}

/// `vg_aes_ccm_seal`: its `_aes_cbc` or `_aesni_cbc` implementation on long
/// inputs (`cbc`) if the CPU has its features, else its dispatcher's choice.
///
/// # Safety
///
/// `vg_aes_ccm_seal`'s.
#[allow(clippy::too_many_arguments)]
unsafe fn seal(
    schedule: &[u8; 240],
    rounds: usize,
    nonce: &[u8],
    aad: &[u8],
    data: *mut u8,
    len: usize,
    tag: *mut u8,
    tag_len: usize,
) {
    let (n, nl, a, al) = (nonce.as_ptr(), nonce.len(), aad.as_ptr(), aad.len());
    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    if cbc(al, len) && detected().contains(SEAL_CBC_FEATURES) {
        // SAFETY: the caller's, and the CPU has the features it needs.
        return unsafe { seal_cbc(schedule, rounds, n, nl, a, al, data, len, tag, tag_len) };
    }
    // SAFETY: the caller's. The dispatcher calls only an implementation the
    // CPU has the features of.
    unsafe { vg_aes_ccm_seal_auto(schedule, rounds, n, nl, a, al, data, len, tag, tag_len) }
}

/// `vg_aes_ccm_open`, chosen as `seal` chooses `vg_aes_ccm_seal`.
///
/// # Safety
///
/// `vg_aes_ccm_open`'s.
#[allow(clippy::too_many_arguments)]
unsafe fn open(
    schedule: &[u8; 240],
    rounds: usize,
    nonce: &[u8],
    aad: &[u8],
    data: *mut u8,
    len: usize,
    tag: *const u8,
    tag_len: usize,
) -> u32 {
    let (n, nl, a, al) = (nonce.as_ptr(), nonce.len(), aad.as_ptr(), aad.len());
    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    if cbc(al, len) && detected().contains(OPEN_CBC_FEATURES) {
        // SAFETY: the caller's, and the CPU has the features it needs.
        return unsafe { open_cbc(schedule, rounds, n, nl, a, al, data, len, tag, tag_len) };
    }
    // SAFETY: the caller's. The dispatcher calls only an implementation the
    // CPU has the features of.
    unsafe { vg_aes_ccm_open_auto(schedule, rounds, n, nl, a, al, data, len, tag, tag_len) }
}

/// Fails to compile unless `T` is a tag length Appendix A.1 allows: 4, 6,
/// 8, 10, 12, 14 or 16 bytes.
macro_rules! assert_tag_length {
    ($t:expr) => {
        const {
            assert!(
                matches!($t, 4 | 6 | 8 | 10 | 12 | 14 | 16),
                "an AES-CCM tag is 4, 6, 8, 10, 12, 14 or 16 bytes long"
            )
        }
    };
}

/// Why an AES-CCM operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The nonce is not 7 to 13 bytes long (Appendix A.1).
    InvalidNonceLength,
    /// The payload is too long for the nonce: at least `2^(8 (15 − n))`
    /// bytes for a nonce of `n` bytes (Appendix A.1).
    InvalidTextLength,
    /// The tag does not match: the ciphertext, the associated data or the
    /// nonce is not what was authenticated under this key.
    TagMismatch,
}

crate::error::impl_error! {
    Error {
        InvalidNonceLength => "invalid AES-CCM nonce length",
        InvalidTextLength => "AES-CCM text is too long for the nonce",
        TagMismatch => "AES-CCM tag does not match",
    }
}

/// An AES-CCM key: its AES key schedule.
#[derive(Clone)]
pub struct AesCcm {
    /// The key schedule `vg_aes_expand_key` writes.
    schedule: [u8; 240],
    /// The number of rounds of AES.
    rounds: usize,
}

impl Drop for AesCcm {
    /// Wipes the key schedule.
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}

/// Checks the nonce's length and the payload's (Appendix A.1): a nonce of
/// `n` bytes, from 7 to 13, leaves `q = 15 − n` bytes for the payload's
/// length, which must be less than `2^(8q)`.
fn check(nonce: &[u8], len: usize) -> Result<(), Error> {
    if !(7..=13).contains(&nonce.len()) {
        return Err(Error::InvalidNonceLength);
    }
    let q = 15 - nonce.len();
    // `len < 2^(8q)`; for `q = 8` every `usize` is.
    if q < 8 && (len as u64) >> (8 * q) != 0 {
        return Err(Error::InvalidTextLength);
    }
    Ok(())
}

impl AesCcm {
    /// Prepares `key`, which must be 16, 24 or 32 bytes long.
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(InvalidKeyLength);
        }
        let mut k = AesCcm {
            schedule: [0; 240],
            rounds: key.len() / 4 + 6,
        };
        // SAFETY: `key` is valid for reads of `key.len()` bytes, which is 16,
        // 24 or 32, and `k.schedule` for reads and writes of 240 bytes. They
        // are distinct objects, so they do not overlap, nor do they overlap
        // the return address on the stack or the stack below it, and neither
        // wraps around the end of the address space. The dispatcher calls
        // only an implementation the CPU has the features of.
        unsafe { vg_aes_expand_key_auto(key.as_ptr(), key.len(), &mut k.schedule) };
        Ok(k)
    }

    /// Generation-encryption (§6.1) with a tag of `T` bytes: encrypts `data`
    /// in place under `nonce` (7 to 13 bytes), and returns the tag, which
    /// authenticates the plaintext, `aad` and `nonce`. The ciphertext of
    /// §6.1 is `data` followed by the tag. A nonce must never be used twice
    /// with the same key.
    ///
    /// `T` must be 4, 6, 8, 10, 12, 14 or 16 (Appendix A.1); any other length
    /// is an error when the call is compiled.
    pub fn encrypt_in_place<const T: usize>(
        &self,
        nonce: &[u8],
        aad: &[u8],
        data: &mut [u8],
    ) -> Result<[u8; T], Error> {
        assert_tag_length!(T);
        check(nonce, data.len())?;
        let mut tag = [0u8; T];
        // SAFETY: `self.schedule` is the key schedule `vg_aes_expand_key`
        // wrote for `self.rounds` (10, 12 or 14) rounds, valid for reads of
        // 240 bytes. `nonce` (7 to 13 bytes) and `aad` are valid for reads
        // of their lengths, `data` for reads and writes of `data.len()`
        // bytes, which `check` has checked is less than `2^(8 (15 −
        // nonce.len()))`, and `tag` for reads and writes of `T` bytes, a
        // length Appendix A.1 allows (`assert_tag_length`). `data` and `tag`
        // are unique borrows, so they overlap neither each other nor the
        // other buffers; no buffer overlaps the arguments on the stack, the
        // return address or the stack below it, and none wraps around the
        // end of the address space.
        unsafe {
            seal(
                &self.schedule,
                self.rounds,
                nonce,
                aad,
                data.as_mut_ptr(),
                data.len(),
                tag.as_mut_ptr(),
                T,
            )
        };
        Ok(tag)
    }

    /// Decryption-verification (§6.2) with a tag of `T` bytes: if `tag`
    /// authenticates the ciphertext in `data`, `aad` and `nonce`, decrypts
    /// `data` in place. Otherwise returns an error and overwrites `data`
    /// with zeros.
    ///
    /// `T` must be 4, 6, 8, 10, 12, 14 or 16 (Appendix A.1); any other length
    /// is an error when the call is compiled.
    pub fn decrypt_in_place<const T: usize>(
        &self,
        nonce: &[u8],
        aad: &[u8],
        data: &mut [u8],
        tag: &[u8; T],
    ) -> Result<(), Error> {
        assert_tag_length!(T);
        check(nonce, data.len())?;
        // SAFETY: as in `encrypt_in_place`, with the received tag `tag`
        // valid for reads of `T` bytes; `tag` is a shared borrow, which
        // `data`, a unique one, does not overlap.
        let ok = unsafe {
            open(
                &self.schedule,
                self.rounds,
                nonce,
                aad,
                data.as_mut_ptr(),
                data.len(),
                tag.as_ptr(),
                T,
            )
        };
        // `open`'s contract leaves the plaintext in `data` if it returns 1,
        // and zeros otherwise.
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::TagMismatch)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{AesCcm, Error, InvalidKeyLength};

    /// The `_aes_cbc` (or `_aesni_cbc`) instances run for more than 32 bytes
    /// of associated data and payload together, the others otherwise.
    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    #[test]
    fn cbc() {
        use super::cbc;
        assert!(!cbc(0, 0));
        assert!(!cbc(16, 16));
        assert!(!cbc(0, 32));
        assert!(!cbc(32, 0));
        assert!(cbc(16, 17));
        assert!(cbc(33, 0));
        assert!(cbc(0, 33));
        assert!(cbc(usize::MAX, usize::MAX));
    }

    #[test]
    fn key_lengths() {
        let key = [0u8; 40];
        for n in [0, 15, 17, 23, 25, 31, 33, 40] {
            assert_eq!(AesCcm::new(&key[..n]).err(), Some(InvalidKeyLength));
        }
    }

    #[test]
    fn text_lengths() {
        let k = AesCcm::new(&[0; 16]).unwrap();
        // A 13-byte nonce leaves 2 bytes for the length: at most 65535.
        let mut data = [1u8; 1 << 16];
        assert_eq!(
            k.encrypt_in_place::<16>(&[0; 13], &[], &mut data),
            Err(Error::InvalidTextLength)
        );
        assert_eq!(
            k.decrypt_in_place(&[0; 13], &[], &mut data, &[0; 16]),
            Err(Error::InvalidTextLength)
        );
        assert!(data.iter().all(|&b| b == 1));
        let data = &mut data[..(1 << 16) - 1];
        let tag = k.encrypt_in_place::<16>(&[0; 13], &[], data).unwrap();
        k.decrypt_in_place(&[0; 13], &[], data, &tag).unwrap();
        assert!(data.iter().all(|&b| b == 1));
    }
}
