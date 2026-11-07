//! The AEADs of the cipher suites, with 12-byte nonces and 16-byte tags.

use rustls::crypto::cipher::OutboundPlain;
use rustls::error::{ApiMisuse, Error};
use verified_garbage::aes_gcm::AesGcm;
use verified_garbage::chacha20poly1305::ChaCha20Poly1305;

pub(crate) const TAG_LEN: usize = 16;

/// An AEAD key: AES-GCM (128- or 256-bit) or ChaCha20-Poly1305. Each lives
/// in a boxed record encrypter or decrypter, so its size does not matter.
#[allow(clippy::large_enum_variant)]
pub(crate) enum Key {
    AesGcm(AesGcm),
    ChaCha20Poly1305(ChaCha20Poly1305),
}

/// Which AEAD a cipher suite uses.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Algorithm {
    Aes128Gcm,
    Aes256Gcm,
    ChaCha20Poly1305,
}

impl Algorithm {
    pub(crate) const fn key_len(self) -> usize {
        match self {
            Self::Aes128Gcm => 16,
            Self::Aes256Gcm | Self::ChaCha20Poly1305 => 32,
        }
    }

    /// The key `key`, which must be [`key_len`](Self::key_len) bytes long
    /// (rustls guarantees it for the keys it derives).
    pub(crate) fn key(self, key: &[u8]) -> Key {
        assert_eq!(key.len(), self.key_len());
        match self {
            Self::Aes128Gcm | Self::Aes256Gcm => Key::AesGcm(AesGcm::new(key).unwrap()),
            Self::ChaCha20Poly1305 => {
                Key::ChaCha20Poly1305(ChaCha20Poly1305::new(key.try_into().unwrap()))
            }
        }
    }
}

impl Key {
    /// Encrypts the plaintext `plain ‖ extra` into `out`, which is exactly as
    /// long, returning the tag. Both AEADs read the pieces where they are
    /// and write only `out`; a plaintext of more pieces than `encrypt`
    /// takes is copied into `out` and encrypted there.
    pub(crate) fn seal_to(
        &self,
        nonce: &[u8; 12],
        aad: &[u8],
        plain: &OutboundPlain<'_>,
        extra: &[u8],
        out: &mut [u8],
    ) -> Result<[u8; TAG_LEN], ()> {
        debug_assert_eq!(out.len(), plain.len() + extra.len());
        // The usual record, one chunk, without the array below, whose
        // initialization costs about a sixth of a 1 KiB record.
        if let Some(p) = plain.single_chunk() {
            return self.encrypt(nonce, aad, &[p, extra], out);
        }
        // `encrypt` takes at most `MAX_PIECES` pieces (the same for both).
        const MAX_PIECES: usize = AesGcm::MAX_PIECES;
        const _: () = assert!(ChaCha20Poly1305::MAX_PIECES == MAX_PIECES);
        if plain.chunks().count() < MAX_PIECES {
            let mut pieces: [&[u8]; MAX_PIECES] = [&[]; MAX_PIECES];
            let mut n = 0;
            for piece in plain.chunks().chain([extra]) {
                pieces[n] = piece;
                n += 1;
            }
            return self.encrypt(nonce, aad, &pieces[..n], out);
        }
        let mut used = 0;
        for piece in plain.chunks().chain([extra]) {
            out[used..used + piece.len()].copy_from_slice(piece);
            used += piece.len();
        }
        self.seal(nonce, aad, out)
    }

    /// Encrypts the concatenation of `pieces` into `out`, returning the tag.
    fn encrypt(
        &self,
        nonce: &[u8; 12],
        aad: &[u8],
        pieces: &[&[u8]],
        out: &mut [u8],
    ) -> Result<[u8; TAG_LEN], ()> {
        match self {
            Self::AesGcm(k) => k.encrypt(nonce, aad, pieces, out).map_err(|_| ()),
            Self::ChaCha20Poly1305(k) => k.encrypt(nonce, aad, pieces, out).map_err(|_| ()),
        }
    }

    /// Encrypts `data` in place, returning the tag.
    pub(crate) fn seal(
        &self,
        nonce: &[u8; 12],
        aad: &[u8],
        data: &mut [u8],
    ) -> Result<[u8; TAG_LEN], ()> {
        match self {
            Self::AesGcm(k) => k.encrypt_in_place(nonce, aad, data).map_err(|_| ()),
            Self::ChaCha20Poly1305(k) => k.encrypt_in_place(nonce, aad, data).map_err(|_| ()),
        }
    }

    /// Decrypts `data`, which ends with its tag, in place: the length of
    /// the plaintext, which is the prefix of `data`.
    pub(crate) fn open(&self, nonce: &[u8; 12], aad: &[u8], data: &mut [u8]) -> Result<usize, ()> {
        let Some(text_len) = data.len().checked_sub(TAG_LEN) else {
            return Err(());
        };
        let (text, tag) = data.split_at_mut(text_len);
        let tag: &[u8; TAG_LEN] = (&*tag).try_into().unwrap();
        match self {
            Self::AesGcm(k) => k.decrypt_in_place(nonce, aad, text, tag).map_err(|_| ())?,
            Self::ChaCha20Poly1305(k) => {
                k.decrypt_in_place(nonce, aad, text, tag).map_err(|_| ())?
            }
        }
        Ok(text_len)
    }
}

/// The first `len` bytes of `out`, where a record of that length is written.
pub(crate) fn record_region(out: &mut [u8], len: usize) -> Result<&mut [u8], Error> {
    let provided = out.len();
    out.get_mut(..len).ok_or_else(|| {
        ApiMisuse::EncryptBufferTooSmall {
            required: len,
            provided,
        }
        .into()
    })
}
