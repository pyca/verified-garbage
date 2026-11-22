//! The AEADs of the cipher suites, with 12-byte nonces and 16-byte tags.

use alloc::vec::Vec;

use rustls::crypto::cipher::{EncodableVersion, OutboundPlain, encode_record_header};
use rustls::enums::ContentType;
use rustls::error::Error;
use verified_garbage::aead::aes_gcm::AesGcm;
use verified_garbage::aead::chacha20poly1305::ChaCha20Poly1305;

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
    /// Appends the plaintext `plain ‖ extra` to `out`, seals it there and
    /// appends its tag: one copy of the plaintext, which a record's buffer
    /// needs anyway, rather than writing every byte of it twice (zeroed,
    /// then encrypted into from where the plaintext is).
    pub(crate) fn seal_append(
        &self,
        nonce: &[u8; 12],
        aad: &[u8],
        plain: &OutboundPlain<'_>,
        extra: &[u8],
        out: &mut Vec<u8>,
    ) -> Result<(), ()> {
        let start = out.len();
        out.reserve(plain.len() + extra.len() + TAG_LEN);
        for piece in plain.chunks() {
            out.extend_from_slice(piece);
        }
        out.extend_from_slice(extra);
        let tag = self.seal(nonce, aad, &mut out[start..])?;
        out.extend_from_slice(&tag);
        Ok(())
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

/// Appends to `out` the header of a record of type `typ`, `version` and a
/// payload of `len` bytes.
pub(crate) fn append_header(
    out: &mut Vec<u8>,
    typ: ContentType,
    version: EncodableVersion,
    len: usize,
) -> Result<(), Error> {
    let len = u16::try_from(len).map_err(|_| Error::EncryptError)?;
    out.extend_from_slice(&encode_record_header(typ, version, len));
    Ok(())
}
