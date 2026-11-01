//! ChaCha20-Poly1305 (RFC 8439 §2.8), with a 96-bit nonce.
//!
//! Encryption and decryption are the verified assembly functions
//! `vg_chacha20_poly1305_seal` and `vg_chacha20_poly1305_open` (contracts
//! `VG.Spec.ChaCha20Poly1305.sealContract` and `openContract`); this module
//! only chooses the implementation and checks the length limit. They take the
//! key, the nonce and the tag by pointer, and keep their working space on
//! their own stack, zeroing it before they return.
//!
//! Their variants, with the same contracts, are those of ChaCha20's
//! `crate::chacha20::Backend`, each with its suffix. On x86-64, `select`
//! chooses among `_ifma`, `_avx512vl`, `_avx512` and `_avx2`, in this order,
//! on CPUs with the features their `_FEATURES` constants name (`_ifma`'s of
//! both `seal` and `open`); elsewhere it chooses as `Backend::select` does
//! for ChaCha20: on x86, `_ssse3`; on AArch64, `_sve2`, then `_neon`. The
//! tests check that each variant needs no feature that this choice does not
//! check.
//!
//! [`ChaCha20Poly1305::encrypt`] encrypts out of place, from a plaintext in
//! pieces (a list of slices, such as a record's payload and TLS 1.3's
//! content type, or a single one) into one output buffer: one call of
//! `vg_chacha20_poly1305_seal_gather`
//! (`VG.Spec.ChaCha20Poly1305.sealGatherContract`), or its variant of the
//! same suffix.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use core::mem::MaybeUninit;

#[cfg(target_arch = "x86_64")]
use crate::arch::chacha20poly1305::{
    VG_CHACHA20_POLY1305_OPEN_IFMA_FEATURES, VG_CHACHA20_POLY1305_SEAL_AVX2_FEATURES,
    VG_CHACHA20_POLY1305_SEAL_AVX512_FEATURES, VG_CHACHA20_POLY1305_SEAL_AVX512VL_FEATURES,
    VG_CHACHA20_POLY1305_SEAL_IFMA_FEATURES, vg_chacha20_poly1305_open_avx2,
    vg_chacha20_poly1305_open_avx512, vg_chacha20_poly1305_open_avx512vl,
    vg_chacha20_poly1305_open_ifma, vg_chacha20_poly1305_seal_avx2,
    vg_chacha20_poly1305_seal_avx512, vg_chacha20_poly1305_seal_avx512vl,
    vg_chacha20_poly1305_seal_gather_avx2, vg_chacha20_poly1305_seal_gather_avx512,
    vg_chacha20_poly1305_seal_gather_avx512vl, vg_chacha20_poly1305_seal_gather_ifma,
    vg_chacha20_poly1305_seal_ifma,
};
use crate::arch::chacha20poly1305::{
    vg_chacha20_poly1305_open, vg_chacha20_poly1305_seal, vg_chacha20_poly1305_seal_gather,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::chacha20poly1305::{
    vg_chacha20_poly1305_open_neon, vg_chacha20_poly1305_open_sve2,
    vg_chacha20_poly1305_seal_gather_neon, vg_chacha20_poly1305_seal_gather_sve2,
    vg_chacha20_poly1305_seal_neon, vg_chacha20_poly1305_seal_sve2,
};
#[cfg(target_arch = "x86")]
use crate::arch::chacha20poly1305::{
    vg_chacha20_poly1305_open_ssse3, vg_chacha20_poly1305_seal_gather_ssse3,
    vg_chacha20_poly1305_seal_ssse3,
};
use crate::chacha20::Backend;
use crate::cpu::detected;
use crate::zeroize::zeroize;
use verified_garbage_cpu::Features;

/// The best implementation a CPU with the features `f` can run (`open`'s
/// variants need the same features as `seal`'s, see the tests, but for
/// `open_ifma`, which also needs `vg_chacha20_apply_avx512vl`'s).
#[cfg(target_arch = "x86_64")]
fn select(f: Features) -> Backend {
    Backend::select_for(
        f,
        Features::all(&[
            VG_CHACHA20_POLY1305_SEAL_IFMA_FEATURES,
            VG_CHACHA20_POLY1305_OPEN_IFMA_FEATURES,
        ]),
        VG_CHACHA20_POLY1305_SEAL_AVX512VL_FEATURES,
        VG_CHACHA20_POLY1305_SEAL_AVX512_FEATURES,
        VG_CHACHA20_POLY1305_SEAL_AVX2_FEATURES,
    )
}

/// The best implementation a CPU with the features `f` can run.
#[cfg(not(target_arch = "x86_64"))]
fn select(f: Features) -> Backend {
    Backend::select(f)
}

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
    /// plaintext.
    InvalidOutputLength,
    /// More than [`ChaCha20Poly1305::MAX_PIECES`] pieces of plaintext for
    /// [`ChaCha20Poly1305::encrypt`].
    TooManyPieces,
}

crate::error::impl_error! {
    Error {
        InvalidTextLength => "ChaCha20-Poly1305 text is too long",
        TagMismatch => "ChaCha20-Poly1305 tag does not match",
        InvalidOutputLength => "ChaCha20-Poly1305 output is not as long as the plaintext",
        TooManyPieces => "too many pieces of ChaCha20-Poly1305 plaintext",
    }
}

/// The AEAD with a key.
#[derive(Clone)]
pub struct ChaCha20Poly1305 {
    key: [u8; 32],
    /// The variants of `seal`, `open` and `seal_gather` to call.
    backend: Backend,
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
        ChaCha20Poly1305 {
            key: *key,
            backend: select(detected()),
        }
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
        let seal = match self.backend {
            Backend::Scalar => vg_chacha20_poly1305_seal,
            #[cfg(target_arch = "aarch64")]
            Backend::Neon => vg_chacha20_poly1305_seal_neon,
            #[cfg(target_arch = "aarch64")]
            Backend::Sve2 => vg_chacha20_poly1305_seal_sve2,
            #[cfg(target_arch = "x86_64")]
            Backend::Avx2 => vg_chacha20_poly1305_seal_avx2,
            #[cfg(target_arch = "x86_64")]
            Backend::Avx512 => vg_chacha20_poly1305_seal_avx512,
            #[cfg(target_arch = "x86_64")]
            Backend::Avx512Vl => vg_chacha20_poly1305_seal_avx512vl,
            #[cfg(target_arch = "x86_64")]
            Backend::Ifma => vg_chacha20_poly1305_seal_ifma,
            #[cfg(target_arch = "x86")]
            Backend::Ssse3 => vg_chacha20_poly1305_seal_ssse3,
        };
        let mut tag = [0; 16];
        // SAFETY: `self.key` is valid for reads of 32 bytes, `nonce` for
        // reads of 12, `aad` for reads of `aad.len()` bytes, `data` for reads
        // and writes of `data.len()` bytes and `tag` for writes of 16 bytes;
        // `data` and `tag` are unique borrows (and `tag` a local), so they
        // overlap neither each other nor the shared borrows `self.key`,
        // `nonce` and `aad`, nor anything on the stack (the return address,
        // any arguments, and the stack below the stack pointer that the
        // function's frame and calls use), and no Rust object wraps around
        // the end of the address space. The CPU has the features of the
        // implementation selected (see `features` in the tests).
        unsafe {
            seal(
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
        let seal = match self.backend {
            Backend::Scalar => vg_chacha20_poly1305_seal_gather,
            #[cfg(target_arch = "aarch64")]
            Backend::Neon => vg_chacha20_poly1305_seal_gather_neon,
            #[cfg(target_arch = "aarch64")]
            Backend::Sve2 => vg_chacha20_poly1305_seal_gather_sve2,
            #[cfg(target_arch = "x86_64")]
            Backend::Avx2 => vg_chacha20_poly1305_seal_gather_avx2,
            #[cfg(target_arch = "x86_64")]
            Backend::Avx512 => vg_chacha20_poly1305_seal_gather_avx512,
            #[cfg(target_arch = "x86_64")]
            Backend::Avx512Vl => vg_chacha20_poly1305_seal_gather_avx512vl,
            #[cfg(target_arch = "x86_64")]
            Backend::Ifma => vg_chacha20_poly1305_seal_gather_ifma,
            #[cfg(target_arch = "x86")]
            Backend::Ssse3 => vg_chacha20_poly1305_seal_gather_ssse3,
        };
        let mut tag = [0; 16];
        // SAFETY: as in `encrypt_in_place`, with `out` valid for reads and
        // writes of `out.len()` bytes; `descs` holds `plaintext.len()`
        // initialized descriptors (a local), each the address and the length
        // of a piece valid for reads, which are `out.len()` bytes in all, at
        // most `P_MAX`. The pieces and the descriptors are read only, and
        // overlap neither `out` (a unique borrow) nor `tag`, nor anything on
        // the stack the function uses.
        unsafe {
            seal(
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
        let open = match self.backend {
            Backend::Scalar => vg_chacha20_poly1305_open,
            #[cfg(target_arch = "aarch64")]
            Backend::Neon => vg_chacha20_poly1305_open_neon,
            #[cfg(target_arch = "aarch64")]
            Backend::Sve2 => vg_chacha20_poly1305_open_sve2,
            #[cfg(target_arch = "x86_64")]
            Backend::Avx2 => vg_chacha20_poly1305_open_avx2,
            #[cfg(target_arch = "x86_64")]
            Backend::Avx512 => vg_chacha20_poly1305_open_avx512,
            #[cfg(target_arch = "x86_64")]
            Backend::Avx512Vl => vg_chacha20_poly1305_open_avx512vl,
            #[cfg(target_arch = "x86_64")]
            Backend::Ifma => vg_chacha20_poly1305_open_ifma,
            #[cfg(target_arch = "x86")]
            Backend::Ssse3 => vg_chacha20_poly1305_open_ssse3,
        };
        // SAFETY: as in `encrypt_in_place`, with `tag` valid for reads of 16
        // bytes: `data` is the only buffer written, a unique borrow, which
        // overlaps none of the shared borrows `self.key`, `nonce`, `aad` and
        // `tag`.
        let ok = unsafe {
            open(
                &self.key,
                nonce,
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
                tag,
            )
        };
        if ok == 1 {
            Ok(())
        } else {
            // `open`'s contract leaves `data` unspecified when the tag is
            // wrong (it may hold the decryption of the forged ciphertext):
            // this, not the verified code, keeps it from being released.
            data.fill(0);
            Err(Error::TagMismatch)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Backend, ChaCha20Poly1305, Error, P_MAX, add_len, check_len, select};
    use crate::cpu::detected;
    #[cfg(target_arch = "x86_64")]
    use verified_garbage_cpu::Features;

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

    /// Every implementation gives the same ciphertext and tag as the scalar
    /// one, and decrypts what any of them encrypted.
    #[test]
    fn implementations_agree() {
        let key = core::array::from_fn(|i| (i * 7) as u8);
        let mut scalar = ChaCha20Poly1305::new(&key);
        scalar.backend = Backend::Scalar;
        let best = ChaCha20Poly1305::new(&key);
        assert_eq!(best.backend, select(detected()));
        let nonce = [9; 12];
        let aad = [4; 20];
        for len in [
            0, 63, 64, 65, 192, 193, 255, 256, 257, 319, 320, 321, 447, 448, 449, 450, 480, 511,
            512, 513, 575, 576, 577, 639, 640, 641, 704, 705, 767, 768, 769, 832, 959, 960, 961,
            1000, 1022, 1023, 1024, 1025, 1088, 1089, 1152, 1153, 1279, 1280, 1281, 1350, 1471,
            1473, 1535, 1984, 1985, 2047, 2048, 2049, 2100, 2304, 2497, 4096, 4097,
        ] {
            let msg: [u8; 4097] = core::array::from_fn(|i| (i * 31) as u8);
            let mut a = msg;
            let mut b = msg;
            let tag = scalar.encrypt_in_place(&nonce, &aad, &mut a[..len]);
            assert_eq!(best.encrypt_in_place(&nonce, &aad, &mut b[..len]), tag);
            let tag = tag.unwrap();
            assert_eq!(a, b);
            assert_eq!(
                best.decrypt_in_place(&nonce, &aad, &mut a[..len], &tag),
                Ok(())
            );
            assert_eq!(
                scalar.decrypt_in_place(&nonce, &aad, &mut b[..len], &tag),
                Ok(())
            );
            assert_eq!(a, msg);
            assert_eq!(b, msg);
        }
    }

    /// The variants for each implementation need the features of both
    /// `vg_chacha20_apply`'s and `vg_poly1305_update`'s variants for the
    /// same CPUs, `open`'s and `seal_gather`'s the same as `seal`'s (but for
    /// `open_ifma`), and `select` chooses by them.
    #[cfg(target_arch = "x86_64")]
    #[test]
    fn features() {
        use crate::arch::chacha20::{
            VG_CHACHA20_APPLY_AVX2_FEATURES, VG_CHACHA20_APPLY_AVX512_FEATURES,
            VG_CHACHA20_APPLY_AVX512VL_FEATURES,
        };
        use crate::arch::chacha20poly1305::{
            VG_CHACHA20_POLY1305_OPEN_AVX2_FEATURES, VG_CHACHA20_POLY1305_OPEN_AVX512_FEATURES,
            VG_CHACHA20_POLY1305_OPEN_AVX512VL_FEATURES, VG_CHACHA20_POLY1305_OPEN_IFMA_FEATURES,
            VG_CHACHA20_POLY1305_SEAL_AVX2_FEATURES, VG_CHACHA20_POLY1305_SEAL_AVX512_FEATURES,
            VG_CHACHA20_POLY1305_SEAL_AVX512VL_FEATURES,
            VG_CHACHA20_POLY1305_SEAL_GATHER_AVX2_FEATURES,
            VG_CHACHA20_POLY1305_SEAL_GATHER_AVX512_FEATURES,
            VG_CHACHA20_POLY1305_SEAL_GATHER_AVX512VL_FEATURES,
            VG_CHACHA20_POLY1305_SEAL_GATHER_IFMA_FEATURES,
            VG_CHACHA20_POLY1305_SEAL_IFMA_FEATURES,
        };
        use crate::arch::poly1305::{
            VG_POLY1305_UPDATE_AVX2_FEATURES, VG_POLY1305_UPDATE_AVX512_FEATURES,
            VG_POLY1305_UPDATE_IFMA_FEATURES,
        };
        let avx2 = Features::all(&[
            VG_CHACHA20_APPLY_AVX2_FEATURES,
            VG_POLY1305_UPDATE_AVX2_FEATURES,
        ]);
        let avx512 = Features::all(&[
            VG_CHACHA20_APPLY_AVX512_FEATURES,
            VG_POLY1305_UPDATE_AVX512_FEATURES,
        ]);
        assert_eq!(VG_CHACHA20_POLY1305_SEAL_AVX2_FEATURES, avx2);
        assert_eq!(VG_CHACHA20_POLY1305_OPEN_AVX2_FEATURES, avx2);
        assert_eq!(VG_CHACHA20_POLY1305_SEAL_GATHER_AVX2_FEATURES, avx2);
        assert_eq!(VG_CHACHA20_POLY1305_SEAL_AVX512_FEATURES, avx512);
        assert_eq!(VG_CHACHA20_POLY1305_OPEN_AVX512_FEATURES, avx512);
        assert_eq!(VG_CHACHA20_POLY1305_SEAL_GATHER_AVX512_FEATURES, avx512);
        let avx512vl = Features::all(&[
            VG_CHACHA20_APPLY_AVX512VL_FEATURES,
            VG_POLY1305_UPDATE_AVX512_FEATURES,
        ]);
        assert_eq!(VG_CHACHA20_POLY1305_SEAL_AVX512VL_FEATURES, avx512vl);
        assert_eq!(VG_CHACHA20_POLY1305_OPEN_AVX512VL_FEATURES, avx512vl);
        assert_eq!(VG_CHACHA20_POLY1305_SEAL_GATHER_AVX512VL_FEATURES, avx512vl);
        let ifma = Features::all(&[
            VG_CHACHA20_APPLY_AVX512_FEATURES,
            VG_POLY1305_UPDATE_IFMA_FEATURES,
        ]);
        assert_eq!(VG_CHACHA20_POLY1305_SEAL_IFMA_FEATURES, ifma);
        // `open_ifma` also needs `vg_chacha20_apply_avx512vl`'s features.
        let ifma_open = Features::all(&[ifma, VG_CHACHA20_APPLY_AVX512VL_FEATURES]);
        assert_eq!(VG_CHACHA20_POLY1305_OPEN_IFMA_FEATURES, ifma_open);
        assert_eq!(VG_CHACHA20_POLY1305_SEAL_GATHER_IFMA_FEATURES, ifma);
        assert_eq!(select(avx2), Backend::Avx2);
        assert_eq!(select(avx512), Backend::Avx512);
        assert_eq!(select(avx512vl), Backend::Avx512Vl);
        assert_eq!(select(ifma_open), Backend::Ifma);
        assert_eq!(select(Features::all(&[avx512vl, ifma])), Backend::Ifma);
        assert_ne!(select(ifma), Backend::Ifma);
        // AVX-512F alone is not enough: the `_avx512` variants also need
        // `VG_POLY1305_UPDATE_AVX512_FEATURES`.
        assert_eq!(select(VG_CHACHA20_APPLY_AVX512_FEATURES), Backend::Scalar);
        assert_eq!(
            select(Features(verified_garbage_cpu::feature::AVX)),
            Backend::Scalar
        );
    }

    /// On x86, the SSSE3 variants (`seal`, `open` and `seal_gather`) need
    /// the features of `vg_chacha20_apply_ssse3` (which `select` checks),
    /// and `select` chooses them with SSSE3.
    #[cfg(target_arch = "x86")]
    #[test]
    fn features() {
        use crate::arch::chacha20::VG_CHACHA20_APPLY_SSSE3_FEATURES;
        use crate::arch::chacha20poly1305::{
            VG_CHACHA20_POLY1305_OPEN_SSSE3_FEATURES,
            VG_CHACHA20_POLY1305_SEAL_GATHER_SSSE3_FEATURES,
            VG_CHACHA20_POLY1305_SEAL_SSSE3_FEATURES,
        };
        use verified_garbage_cpu::Features;
        let ssse3 = VG_CHACHA20_APPLY_SSSE3_FEATURES;
        assert_eq!(VG_CHACHA20_POLY1305_SEAL_SSSE3_FEATURES, ssse3);
        assert_eq!(VG_CHACHA20_POLY1305_OPEN_SSSE3_FEATURES, ssse3);
        assert_eq!(VG_CHACHA20_POLY1305_SEAL_GATHER_SSSE3_FEATURES, ssse3);
        assert_eq!(select(ssse3), Backend::Ssse3);
        assert_eq!(select(Features(0)), Backend::Scalar);
    }

    /// On AArch64, the SVE2 variants need the features of
    /// `vg_chacha20_apply_sve2`, `open`'s and `seal_gather`'s the same as
    /// `seal`'s, and `select` chooses them with SVE2 (and the NEON ones
    /// without).
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn features() {
        use crate::arch::chacha20::VG_CHACHA20_APPLY_SVE2_FEATURES;
        use crate::arch::chacha20poly1305::{
            VG_CHACHA20_POLY1305_OPEN_SVE2_FEATURES,
            VG_CHACHA20_POLY1305_SEAL_GATHER_SVE2_FEATURES,
            VG_CHACHA20_POLY1305_SEAL_SVE2_FEATURES,
        };
        use verified_garbage_cpu::Features;
        let sve2 = VG_CHACHA20_APPLY_SVE2_FEATURES;
        assert_eq!(VG_CHACHA20_POLY1305_SEAL_SVE2_FEATURES, sve2);
        assert_eq!(VG_CHACHA20_POLY1305_OPEN_SVE2_FEATURES, sve2);
        assert_eq!(VG_CHACHA20_POLY1305_SEAL_GATHER_SVE2_FEATURES, sve2);
        assert_eq!(
            select(Features::all(&[
                Features(verified_garbage_cpu::feature::NEON),
                VG_CHACHA20_APPLY_SVE2_FEATURES
            ])),
            Backend::Sve2
        );
        assert_eq!(
            select(Features(verified_garbage_cpu::feature::NEON)),
            Backend::Neon
        );
    }
}
