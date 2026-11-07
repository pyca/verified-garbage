//! ChaCha20-Poly1305 (RFC 8439 §2.8), with a 96-bit nonce.
//!
//! A nonce must never be used twice with the same key.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use core::mem::MaybeUninit;

#[cfg(any(
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
))]
use crate::arch::dispatch::chacha20poly1305::vg_chacha20_poly1305_open_to_auto;
use crate::arch::dispatch::chacha20poly1305::{
    vg_chacha20_poly1305_open_auto, vg_chacha20_poly1305_seal_auto,
    vg_chacha20_poly1305_seal_gather_auto,
};
use crate::zeroize::zeroize;

/// The largest plaintext RFC 8439 allows (`P_MAX`, §2.8): 2³² − 1 blocks of
/// 64 bytes, as the block counter starts at 1.
const P_MAX: u64 = (1 << 38) - 64;

/// `len + n`, if it is at most `P_MAX`.
fn add_len(len: u64, n: usize) -> Result<u64, Error> {
    len.checked_add(n as u64)
        .filter(|&sum| sum <= P_MAX)
        .ok_or(Error::InvalidTextLength)
}

/// Checks that a text of `len` bytes is at most `P_MAX` long.
fn check_len(len: usize) -> Result<(), Error> {
    add_len(0, len).map(|_| ())
}

/// Why a ChaCha20-Poly1305 operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The plaintext or ciphertext is longer than `2^38 − 64` bytes (RFC
    /// 8439's `P_MAX`, §2.8).
    InvalidTextLength,
    /// The tag does not match: the ciphertext, the additional data or the
    /// nonce is not what was authenticated under this key.
    TagMismatch,
    /// The output of [`ChaCha20Poly1305::encrypt`] is not as long as the
    /// plaintext, or that of `ChaCha20Poly1305::decrypt` as the ciphertext.
    InvalidOutputLength,
    /// More than [`ChaCha20Poly1305::MAX_PIECES`] pieces of plaintext for
    /// [`ChaCha20Poly1305::encrypt`].
    TooManyPieces,
}

crate::error::impl_error! {
    Error {
        InvalidTextLength => "ChaCha20-Poly1305 text is too long",
        TagMismatch => "ChaCha20-Poly1305 tag does not match",
        InvalidOutputLength => "ChaCha20-Poly1305 output is not as long as its input",
        TooManyPieces => "too many pieces of ChaCha20-Poly1305 plaintext",
    }
}

/// The AEAD with a key.
#[derive(Clone)]
pub struct ChaCha20Poly1305 {
    key: [u8; 32],
}

impl Drop for ChaCha20Poly1305 {
    /// Wipes the key.
    fn drop(&mut self) {
        zeroize(&mut self.key);
    }
}

impl ChaCha20Poly1305 {
    /// The size of a key, in bytes.
    pub const KEY_SIZE: usize = 32;
    /// The size of a nonce, in bytes.
    pub const NONCE_SIZE: usize = 12;
    /// The size of a tag, in bytes.
    pub const TAG_SIZE: usize = 16;

    /// The AEAD with the key `key`.
    pub fn new(key: &[u8; 32]) -> Self {
        ChaCha20Poly1305 { key: *key }
    }

    /// Encrypts `data` in place, with the nonce `nonce` and the additional
    /// data `aad`, and returns the tag.
    pub fn encrypt_in_place(
        &self,
        nonce: &[u8; 12],
        aad: &[u8],
        data: &mut [u8],
    ) -> Result<[u8; 16], Error> {
        // Check the length before encrypting anything.
        check_len(data.len())?;
        let mut tag = [0; 16];
        // SAFETY: `self.key` is valid for reads of 32 bytes, `nonce` for
        // reads of 12, `aad` for reads of `aad.len()` bytes, `data` for reads
        // and writes of `data.len()` bytes and `tag` for writes of 16 bytes;
        // `data` and `tag` are unique borrows (and `tag` a local), so they
        // overlap neither each other nor the shared borrows `self.key`,
        // `nonce` and `aad`, nor anything on the stack (the return address,
        // any arguments, and the stack below the stack pointer that the
        // function's frame and calls use), and no Rust object wraps around
        // the end of the address space. The dispatcher calls only an
        // implementation the CPU has the features of.
        unsafe {
            vg_chacha20_poly1305_seal_auto(
                &self.key,
                nonce,
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
                &mut tag,
            )
        };
        Ok(tag)
    }

    /// The most pieces [`encrypt`](Self::encrypt) takes a plaintext in.
    pub const MAX_PIECES: usize = 64;

    /// Encrypts the plaintext made of the pieces `plaintext`, in order, with
    /// the nonce `nonce` and the additional data `aad`, into `out`, which
    /// must be exactly as long as they are in all, and returns the tag. A
    /// plaintext in one buffer is one piece (`&[buf]`); there may be at most
    /// [`MAX_PIECES`](Self::MAX_PIECES).
    pub fn encrypt(
        &self,
        nonce: &[u8; 12],
        aad: &[u8],
        plaintext: &[&[u8]],
        out: &mut [u8],
    ) -> Result<[u8; 16], Error> {
        if plaintext.len() > Self::MAX_PIECES {
            return Err(Error::TooManyPieces);
        }
        let mut len = 0;
        for p in plaintext {
            len = add_len(len, p.len())?;
        }
        if len != out.len() as u64 {
            return Err(Error::InvalidOutputLength);
        }
        // The descriptors of the pieces, as `vg_chacha20_poly1305_seal_gather`
        // takes them: each its address and its length. Only the first
        // `plaintext.len()` are written, and the function reads only those.
        let mut descs = [const { MaybeUninit::<[usize; 2]>::uninit() }; Self::MAX_PIECES];
        for (d, p) in descs.iter_mut().zip(plaintext) {
            d.write([p.as_ptr() as usize, p.len()]);
        }
        let mut tag = [0; 16];
        // SAFETY: as in `encrypt_in_place`, with `out` valid for reads and
        // writes of `out.len()` bytes; `descs` holds `plaintext.len()`
        // initialized descriptors (a local), each the address and the length
        // of a piece valid for reads, which are `out.len()` bytes in all, at
        // most `P_MAX`. The pieces and the descriptors are read only, and
        // overlap neither `out` (a unique borrow) nor `tag`, nor anything on
        // the stack the function uses.
        unsafe {
            vg_chacha20_poly1305_seal_gather_auto(
                &self.key,
                nonce,
                aad.as_ptr(),
                aad.len(),
                descs.as_ptr().cast(),
                plaintext.len(),
                out.as_mut_ptr(),
                out.len(),
                &mut tag,
            )
        };
        Ok(tag)
    }

    /// Decrypts `data` in place, with the nonce `nonce` and the additional
    /// data `aad`, if `tag` authenticates it; otherwise returns
    /// [`Error::TagMismatch`] and zeroes `data`.
    pub fn decrypt_in_place(
        &self,
        nonce: &[u8; 12],
        aad: &[u8],
        data: &mut [u8],
        tag: &[u8; 16],
    ) -> Result<(), Error> {
        check_len(data.len())?;
        // SAFETY: as in `encrypt_in_place`, with `tag` valid for reads of 16
        // bytes: `data` is the only buffer written, a unique borrow, which
        // overlaps none of the shared borrows `self.key`, `nonce`, `aad` and
        // `tag`.
        let ok = unsafe {
            vg_chacha20_poly1305_open_auto(
                &self.key,
                nonce,
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
                tag,
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

    /// Decrypts `ciphertext`, with the nonce `nonce` and the additional data
    /// `aad`, into `out`, which must be exactly as long as it, if `tag`
    /// authenticates it; otherwise returns [`Error::TagMismatch`] and zeroes
    /// `out`. `ciphertext` is read where it is, not copied to `out` first. A
    /// length error leaves `out` as it was.
    #[cfg(any(
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "x86",
        target_arch = "riscv64",
        all(target_arch = "powerpc64", target_endian = "little")
    ))]
    pub fn decrypt(
        &self,
        nonce: &[u8; 12],
        aad: &[u8],
        ciphertext: &[u8],
        tag: &[u8; 16],
        out: &mut [u8],
    ) -> Result<(), Error> {
        check_len(ciphertext.len())?;
        if out.len() != ciphertext.len() {
            return Err(Error::InvalidOutputLength);
        }
        // SAFETY: as in `decrypt_in_place`, with `ciphertext` valid for
        // reads of `ciphertext.len()` bytes, at most `P_MAX` (`check_len`),
        // and `out` for writes of `out.len()`, which is `ciphertext.len()`:
        // `out` is the only buffer written, a unique borrow, which overlaps
        // none of the shared borrows `self.key`, `nonce`, `aad`,
        // `ciphertext` and `tag`.
        let ok = unsafe {
            vg_chacha20_poly1305_open_to_auto(
                &self.key,
                nonce,
                aad.as_ptr(),
                aad.len(),
                ciphertext.as_ptr(),
                ciphertext.len(),
                out.as_mut_ptr(),
                out.len(),
                tag,
            )
        };
        // `open_to`'s contract leaves the plaintext in `out` if it returns
        // 1, and zeros otherwise.
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::TagMismatch)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{ChaCha20Poly1305, Error, P_MAX, add_len, check_len};

    /// Decryption undoes encryption, and rejects any change to the data, the
    /// additional data, the nonce or the tag, zeroing the data.
    #[test]
    fn round_trip() {
        let aead = ChaCha20Poly1305::new(&core::array::from_fn(|i| i as u8));
        let nonce = [7; 12];
        let aad = [1, 2, 3];
        for len in [0, 1, 15, 16, 17, 63, 64, 65, 200] {
            let msg: [u8; 200] = core::array::from_fn(|i| (i * 13) as u8);
            let msg = &msg[..len];
            let mut buf = [0u8; 200];
            let data = &mut buf[..len];
            data.copy_from_slice(msg);
            let tag = aead.encrypt_in_place(&nonce, &aad, data).unwrap();
            let mut copy = [0u8; 200];
            let copy = &mut copy[..len];
            copy.copy_from_slice(data);
            assert_eq!(aead.decrypt_in_place(&nonce, &aad, copy, &tag), Ok(()));
            assert_eq!(copy, msg);
            let mut bad_tag = tag;
            bad_tag[0] ^= 1;
            copy.copy_from_slice(data);
            assert_eq!(
                aead.decrypt_in_place(&nonce, &aad, copy, &bad_tag),
                Err(Error::TagMismatch)
            );
            assert!(copy.iter().all(|&b| b == 0));
            copy.copy_from_slice(data);
            assert_eq!(
                aead.decrypt_in_place(&[8; 12], &aad, copy, &tag),
                Err(Error::TagMismatch)
            );
            copy.copy_from_slice(data);
            assert_eq!(
                aead.decrypt_in_place(&nonce, &aad[..2], copy, &tag),
                Err(Error::TagMismatch)
            );
            if len > 0 {
                copy.copy_from_slice(data);
                copy[len - 1] ^= 0x80;
                assert_eq!(
                    aead.decrypt_in_place(&nonce, &aad, copy, &tag),
                    Err(Error::TagMismatch)
                );
            }
        }
    }

    /// `P_MAX` bytes are allowed and one more are not (a 32-bit length is
    /// always allowed), which no test can reach with real buffers.
    #[test]
    fn length_limit() {
        assert_eq!(check_len(0), Ok(()));
        let max = usize::try_from(P_MAX).unwrap_or(usize::MAX);
        assert_eq!(check_len(max), Ok(()));
        // Only a 64-bit `usize` holds a longer length (a `cfg` rather than a
        // test of the width, so that each architecture runs every line it
        // builds).
        #[cfg(target_pointer_width = "64")]
        assert_eq!(check_len(P_MAX as usize + 1), Err(Error::InvalidTextLength));
        assert_eq!(add_len(P_MAX - 1, 1), Ok(P_MAX));
        assert_eq!(add_len(P_MAX, 1), Err(Error::InvalidTextLength));
        assert_eq!(add_len(u64::MAX, 1), Err(Error::InvalidTextLength));
    }

    /// Out of place, from pieces: the ciphertext and the tag of the
    /// concatenation of the pieces encrypted in place, for any split, at
    /// lengths from 0 to 4097 bytes; and the errors.
    #[test]
    fn encrypt_pieces() {
        let key = core::array::from_fn(|i| (i * 5) as u8);
        let aead = ChaCha20Poly1305::new(&key);
        let nonce = [3; 12];
        let msg: [u8; 4097] = core::array::from_fn(|i| (i * 11) as u8);
        for len in [
            0, 1, 15, 16, 17, 31, 64, 129, 513, 600, 960, 961, 1025, 2049, 4097,
        ] {
            for aad in [&[][..], &[5; 20]] {
                let mut want = msg;
                let want_tag = aead
                    .encrypt_in_place(&nonce, aad, &mut want[..len])
                    .unwrap();
                let m = &msg[..len];
                let (h, q) = (len / 2, len * 3 / 4);
                let one: [&[u8]; 1] = [m];
                let two: [&[u8]; 2] = [&m[..h], &m[h..]];
                let five: [&[u8]; 5] = [&[], &m[..h], &m[h..h], &m[h..q], &m[q..]];
                for pieces in [&one[..], &two, &five] {
                    let mut out = [0u8; 4097];
                    let tag = aead.encrypt(&nonce, aad, pieces, &mut out[..len]);
                    assert_eq!((&out[..len], tag), (&want[..len], Ok(want_tag)));
                }
            }
        }
        let n = ChaCha20Poly1305::MAX_PIECES;
        let mut want = msg;
        let want_tag = aead.encrypt_in_place(&nonce, &[], &mut want[..n]).unwrap();
        let bytes: [&[u8]; ChaCha20Poly1305::MAX_PIECES] = core::array::from_fn(|i| &msg[i..i + 1]);
        let mut out = [0u8; ChaCha20Poly1305::MAX_PIECES];
        let tag = aead.encrypt(&nonce, &[], &bytes, &mut out);
        assert_eq!((&out[..], tag), (&want[..n], Ok(want_tag)));
        let empty = [&msg[..0]; ChaCha20Poly1305::MAX_PIECES + 1];
        assert_eq!(
            aead.encrypt(&nonce, &[], &empty, &mut []),
            Err(Error::TooManyPieces)
        );
        assert_eq!(
            aead.encrypt(&nonce, &[], &[], &mut []),
            aead.encrypt(&nonce, &[], &[&[]], &mut [])
        );
        let mut out = [0u8; 4];
        assert_eq!(
            aead.encrypt(&nonce, &[], &[&msg[..1], &msg[1..3]], &mut out),
            Err(Error::InvalidOutputLength)
        );
    }

    /// `encrypt` agrees with `encrypt_in_place` at every length up to 300
    /// bytes, written at outputs of several alignments.
    #[test]
    fn encrypt_lengths() {
        let aead = ChaCha20Poly1305::new(&core::array::from_fn(|i| (i * 3) as u8));
        let nonce = [9; 12];
        let msg: [u8; 300] = core::array::from_fn(|i| (i * 13) as u8);
        for len in 0..=300 {
            let mut want = msg;
            let want_tag = aead
                .encrypt_in_place(&nonce, &[], &mut want[..len])
                .unwrap();
            for offset in [0, 1, 8, 31, 63] {
                let mut out = [0u8; 364];
                let tag = aead.encrypt(&nonce, &[], &[&msg[..len]], &mut out[offset..offset + len]);
                assert_eq!(
                    (&out[offset..offset + len], tag),
                    (&want[..len], Ok(want_tag))
                );
            }
        }
    }

    /// Out of place: `decrypt` undoes `encrypt_in_place` at every length up
    /// to 300 bytes, from and to buffers at several alignments, leaving the
    /// ciphertext as it was; zeroes the output on a wrong tag; and leaves it
    /// as it was on a length error.
    #[cfg(any(
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "x86",
        target_arch = "riscv64",
        all(target_arch = "powerpc64", target_endian = "little")
    ))]
    #[test]
    fn decrypt_out_of_place() {
        let aead = ChaCha20Poly1305::new(&core::array::from_fn(|i| (i * 9) as u8));
        let nonce = [5; 12];
        let aad = [6; 7];
        let msg: [u8; 300] = core::array::from_fn(|i| (i * 17) as u8);
        for len in 0..=300 {
            let mut ct = [0u8; 364];
            let ct_off = len % 37;
            let ct = &mut ct[ct_off..ct_off + len];
            ct.copy_from_slice(&msg[..len]);
            let tag = aead.encrypt_in_place(&nonce, &aad, ct).unwrap();
            let ct = &*ct;
            for offset in [0, 1, 8, 31, 63] {
                let mut out = [0xAAu8; 364];
                let dst = &mut out[offset..offset + len];
                assert_eq!(aead.decrypt(&nonce, &aad, ct, &tag, dst), Ok(()));
                assert_eq!(dst, &msg[..len]);
            }
            let mut bad = tag;
            bad[15] ^= 0x40;
            let mut out = [0xAAu8; 300];
            assert_eq!(
                aead.decrypt(&nonce, &aad, ct, &bad, &mut out[..len]),
                Err(Error::TagMismatch)
            );
            assert!(out[..len].iter().all(|&b| b == 0));
            assert!(out[len..].iter().all(|&b| b == 0xAA));
        }
        // Lengths the long paths take (whole chunks of 512 bytes, the rests
        // after them, and the paths through the keystream of eight blocks).
        let msg: [u8; 4097] = core::array::from_fn(|i| (i * 13) as u8);
        for len in [
            449, 511, 512, 513, 576, 577, 704, 705, 768, 769, 896, 1024, 1350, 2049, 4097,
        ] {
            let mut ct = [0u8; 4097 + 7];
            let ct = &mut ct[7..7 + len];
            ct.copy_from_slice(&msg[..len]);
            let tag = aead.encrypt_in_place(&nonce, &aad, ct).unwrap();
            let ct = &*ct;
            let mut out = [0xAAu8; 4097 + 3];
            let dst = &mut out[3..3 + len];
            assert_eq!(aead.decrypt(&nonce, &aad, ct, &tag, dst), Ok(()));
            assert_eq!(dst, &msg[..len]);
            let mut bad = tag;
            bad[0] ^= 1;
            assert_eq!(
                aead.decrypt(&nonce, &aad, ct, &bad, dst),
                Err(Error::TagMismatch)
            );
            assert!(dst.iter().all(|&b| b == 0));
        }
        let ct = [1u8; 4];
        let mut out = [0xAAu8; 5];
        assert_eq!(
            aead.decrypt(&nonce, &aad, &ct, &[0; 16], &mut out),
            Err(Error::InvalidOutputLength)
        );
        assert_eq!(
            aead.decrypt(&nonce, &aad, &ct, &[0; 16], &mut out[..3]),
            Err(Error::InvalidOutputLength)
        );
        assert_eq!(out, [0xAA; 5]);
    }
}
