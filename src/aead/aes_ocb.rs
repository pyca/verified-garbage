//! AES-OCB (OCB3, RFC 7253) with 128-, 192- and 256-bit keys.
//!
//! A nonce must never be used twice with the same key. The tag length, 1 to 16
//! bytes, is a type parameter, `T` in [`AesOcb::encrypt_in_place`] and
//! [`AesOcb::decrypt_in_place`], so that it is fixed in the caller's code and
//! never taken from a message (see `crate::aead::aes_gcm`); RFC 7253 §3.1 defines the
//! AEADs with tags of 16, 12 and 8 bytes.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::aes_ocb::{
    vg_aes_ocb_init_auto, vg_aes_ocb_open_auto, vg_aes_ocb_seal_auto,
};
use crate::error::InvalidKeyLength;
use crate::zeroize::zeroize;

/// Fails to compile unless `T` is a tag length OCB allows: 1 to 16 bytes.
macro_rules! assert_tag_length {
    ($t:expr) => {
        const { assert!(matches!($t, 1..=16), "an AES-OCB tag is 1 to 16 bytes long") }
    };
}

/// Why an AES-OCB operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The nonce is not 1 to 15 bytes long (§4.2: at most 120 bits).
    InvalidNonceLength,
    /// The tag does not match: the ciphertext, the associated data or the
    /// nonce is not what was authenticated under this key.
    TagMismatch,
}

crate::error::impl_error! {
    Error {
        InvalidNonceLength => "invalid AES-OCB nonce length",
        TagMismatch => "AES-OCB tag does not match",
    }
}

/// An AES-OCB key: its key context.
#[derive(Clone)]
pub struct AesOcb {
    /// The key context `vg_aes_ocb_init` writes: the key schedule, and `L_*`
    /// in bytes 240–255.
    ctx: [u64; 32],
    /// The number of rounds of AES.
    rounds: usize,
}

impl Drop for AesOcb {
    /// Wipes the key context.
    fn drop(&mut self) {
        zeroize(&mut self.ctx);
    }
}

/// Checks the nonce's length: 1 to 15 bytes.
fn check(nonce: &[u8]) -> Result<(), Error> {
    if (1..=15).contains(&nonce.len()) {
        Ok(())
    } else {
        Err(Error::InvalidNonceLength)
    }
}

impl AesOcb {
    /// Prepares `key`, which must be 16, 24 or 32 bytes long.
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(InvalidKeyLength);
        }
        let mut k = AesOcb {
            ctx: [0; 32],
            rounds: key.len() / 4 + 6,
        };
        // SAFETY: `key` is valid for reads of `key.len()` bytes, which is 16,
        // 24 or 32; `k.ctx` is valid for reads and writes of 256 bytes. They
        // are distinct objects, so they do not overlap, nor do they overlap
        // the return address on the stack or the stack below it, and neither
        // wraps around the end of the address space. The dispatcher calls only
        // an implementation the CPU has the features of.
        unsafe { vg_aes_ocb_init_auto(key.as_ptr(), key.len(), &mut k.ctx) };
        Ok(k)
    }

    /// `OCB-ENCRYPT` (§4.2) with a tag of `T` bytes: encrypts `data` in
    /// place under `nonce` (1 to 15 bytes), and returns the tag, which
    /// authenticates the plaintext, `aad` and `nonce`. The ciphertext of
    /// §4.2 is `data` followed by the tag. A nonce must never be used twice
    /// with the same key.
    ///
    /// `T` must be 1 to 16; any other length is an error when the call is
    /// compiled.
    pub fn encrypt_in_place<const T: usize>(
        &self,
        nonce: &[u8],
        aad: &[u8],
        data: &mut [u8],
    ) -> Result<[u8; T], Error> {
        assert_tag_length!(T);
        check(nonce)?;
        let mut tag = [0u8; T];
        // SAFETY: `self.ctx` is the key context `vg_aes_ocb_init` wrote for
        // `self.rounds` (10, 12 or 14) rounds, valid for reads of 256 bytes.
        // `nonce` (1 to 15 bytes, `check`) and `aad` are valid for reads of
        // their lengths, `data` for reads and writes of `data.len()` bytes,
        // and `tag` for reads and writes of `T` bytes, 1 to 16
        // (`assert_tag_length`). `data` and `tag` are unique borrows, so they
        // overlap neither each other nor the other buffers; no buffer
        // overlaps the arguments on the stack, the return address or the
        // stack below it, and none wraps around the end of the address
        // space. The dispatcher calls only an implementation the CPU has the
        // features of.
        unsafe {
            vg_aes_ocb_seal_auto(
                &self.ctx,
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
                tag.as_mut_ptr(),
                T,
            )
        };
        Ok(tag)
    }

    /// `OCB-DECRYPT` (§4.3) with a tag of `T` bytes: if `tag` authenticates
    /// the ciphertext in `data`, `aad` and `nonce`, decrypts `data` in place.
    /// Otherwise returns an error and overwrites `data` with zeros.
    ///
    /// `T` must be 1 to 16; any other length is an error when the call is
    /// compiled.
    pub fn decrypt_in_place<const T: usize>(
        &self,
        nonce: &[u8],
        aad: &[u8],
        data: &mut [u8],
        tag: &[u8; T],
    ) -> Result<(), Error> {
        assert_tag_length!(T);
        check(nonce)?;
        // SAFETY: as in `encrypt_in_place`, with the received tag `tag`
        // valid for reads of `T` bytes; `tag` is a shared borrow, which
        // `data`, a unique one, does not overlap.
        let ok = unsafe {
            vg_aes_ocb_open_auto(
                &self.ctx,
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
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
    use super::{AesOcb, Error, InvalidKeyLength};

    #[test]
    fn key_lengths() {
        let key = [0u8; 40];
        for n in [0, 15, 17, 23, 25, 31, 33, 40] {
            assert_eq!(AesOcb::new(&key[..n]).err(), Some(InvalidKeyLength));
        }
    }

    #[test]
    fn nonce_lengths() {
        let k = AesOcb::new(&[0; 16]).unwrap();
        let mut data = [1u8; 20];
        for n in [0, 16, 17] {
            let nonce = [0u8; 17];
            assert_eq!(
                k.encrypt_in_place::<16>(&nonce[..n], &[], &mut data),
                Err(Error::InvalidNonceLength)
            );
            assert_eq!(
                k.decrypt_in_place(&nonce[..n], &[], &mut data, &[0; 16]),
                Err(Error::InvalidNonceLength)
            );
        }
        assert!(data.iter().all(|&b| b == 1));
        for n in [1, 15] {
            let nonce = [7u8; 15];
            let tag = k
                .encrypt_in_place::<1>(&nonce[..n], &[2], &mut data)
                .unwrap();
            k.decrypt_in_place(&nonce[..n], &[2], &mut data, &tag)
                .unwrap();
            assert!(data.iter().all(|&b| b == 1));
        }
    }
}
