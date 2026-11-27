//! QUIC packet and header protection (RFC 9001 §5).

use alloc::boxed::Box;

use rustls::crypto::cipher::{AeadKey, Iv, Nonce};
use rustls::error::{ApiMisuse, Error};
use rustls::quic;
use verified_garbage::cipher::aes::AesEcb;
use verified_garbage::cipher::chacha20::ChaCha20;
use zeroize::Zeroizing;

use crate::aead::{self, TAG_LEN};

/// A header protection key: AES (RFC 9001 §5.4.3) or ChaCha20 (§5.4.4). It
/// lives boxed, so its size does not matter.
#[allow(clippy::large_enum_variant)]
enum HeaderProtectionKey {
    Aes(AesEcb),
    ChaCha20(Zeroizing<[u8; 32]>),
}

const SAMPLE_LEN: usize = 16;

impl HeaderProtectionKey {
    /// The first five bytes of the mask of `sample`.
    fn mask(&self, sample: &[u8; SAMPLE_LEN]) -> Zeroizing<[u8; 5]> {
        let mut mask = Zeroizing::new([0u8; 5]);
        match self {
            // AES-ECB of the sample.
            Self::Aes(key) => {
                let mut block = Zeroizing::new(*sample);
                key.encrypt(&mut *block).unwrap();
                mask.copy_from_slice(&block[..5]);
            }
            // The sample is the block counter (little-endian) and the
            // nonce, which is what `ChaCha20` takes as its 16-byte nonce.
            Self::ChaCha20(key) => ChaCha20::new(key, sample).apply_keystream(&mut *mask),
        }
        mask
    }

    fn xor_in_place(
        &self,
        sample: &[u8],
        first: &mut u8,
        packet_number: &mut [u8],
        masked: bool,
    ) -> Result<(), Error> {
        // This implements "Header Protection Application" almost verbatim.
        // <https://datatracker.ietf.org/doc/html/rfc9001#section-5.4.1>
        let sample: &[u8; SAMPLE_LEN] = sample
            .try_into()
            .map_err(|_| ApiMisuse::InvalidQuicHeaderProtectionSampleLength)?;

        let mask = self.mask(sample);
        let (first_mask, pn_mask) = mask.split_first().unwrap();

        // It is OK for the `mask` to be longer than `packet_number`,
        // but a valid `packet_number` will never be longer than `mask`.
        if packet_number.len() > pn_mask.len() {
            return Err(ApiMisuse::InvalidQuicHeaderProtectionPacketNumberLength.into());
        }

        // Infallible from this point on. Before this point, `first` and
        // `packet_number` are unchanged.

        const LONG_HEADER_FORM: u8 = 0x80;
        let bits = match *first & LONG_HEADER_FORM == LONG_HEADER_FORM {
            true => 0x0f,  // Long header: 4 bits masked
            false => 0x1f, // Short header: 5 bits masked
        };

        let first_plain = match masked {
            // When unmasking, use the packet length bits after unmasking
            true => *first ^ (first_mask & bits),
            // When masking, use the packet length bits before masking
            false => *first,
        };
        let pn_len = (first_plain & 0x03) as usize + 1;

        *first ^= first_mask & bits;
        for (dst, m) in packet_number.iter_mut().zip(pn_mask).take(pn_len) {
            *dst ^= m;
        }

        Ok(())
    }
}

impl quic::HeaderProtectionKey for HeaderProtectionKey {
    fn encrypt_in_place(
        &self,
        sample: &[u8],
        first: &mut u8,
        packet_number: &mut [u8],
    ) -> Result<(), Error> {
        self.xor_in_place(sample, first, packet_number, false)
    }

    fn decrypt_in_place(
        &self,
        sample: &[u8],
        first: &mut u8,
        packet_number: &mut [u8],
    ) -> Result<(), Error> {
        self.xor_in_place(sample, first, packet_number, true)
    }

    fn sample_len(&self) -> usize {
        SAMPLE_LEN
    }
}

/// Sealing failing, which only a payload longer than AES-GCM's 2^36 - 32
/// bytes causes (ChaCha20-Poly1305's limit is larger).
fn seal_failed(_: ()) -> Error {
    Error::EncryptError
}

struct PacketKey {
    /// Encrypts or decrypts a packet's payload
    key: aead::Key,
    /// Computes unique nonces for each packet
    iv: Iv,
    /// Confidentiality limit (see [`quic::PacketKey::confidentiality_limit`])
    confidentiality_limit: u64,
    /// Integrity limit (see [`quic::PacketKey::integrity_limit`])
    integrity_limit: u64,
}

impl quic::PacketKey for PacketKey {
    fn encrypt_in_place(
        &self,
        packet_number: u64,
        header: &[u8],
        payload: &mut [u8],
        path_id: Option<u32>,
    ) -> Result<quic::Tag, Error> {
        let nonce = Nonce::quic(path_id, &self.iv, packet_number).to_array()?;
        let tag = self
            .key
            .seal(&nonce, header, payload)
            .map_err(seal_failed)?;
        Ok(quic::Tag::from(&tag[..]))
    }

    fn decrypt_in_place<'a>(
        &self,
        packet_number: u64,
        header: &[u8],
        payload: &'a mut [u8],
        path_id: Option<u32>,
    ) -> Result<&'a [u8], Error> {
        let nonce = Nonce::quic(path_id, &self.iv, packet_number).to_array()?;
        let plain_len = self
            .key
            .open(&nonce, header, payload)
            .map_err(|_| Error::DecryptError)?;
        Ok(&payload[..plain_len])
    }

    fn tag_len(&self) -> usize {
        TAG_LEN
    }

    fn confidentiality_limit(&self) -> u64 {
        self.confidentiality_limit
    }

    fn integrity_limit(&self) -> u64 {
        self.integrity_limit
    }
}

pub(crate) struct KeyBuilder {
    pub(crate) packet_alg: aead::Algorithm,
    pub(crate) confidentiality_limit: u64,
    pub(crate) integrity_limit: u64,
}

impl quic::Algorithm for KeyBuilder {
    fn packet_key(&self, key: AeadKey, iv: Iv) -> Box<dyn quic::PacketKey> {
        Box::new(PacketKey {
            key: self.packet_alg.key(key.as_ref()),
            iv,
            confidentiality_limit: self.confidentiality_limit,
            integrity_limit: self.integrity_limit,
        })
    }

    fn header_protection_key(&self, key: AeadKey) -> Box<dyn quic::HeaderProtectionKey> {
        Box::new(match self.packet_alg {
            // The header protection key is as long as the packet key.
            aead::Algorithm::Aes128Gcm | aead::Algorithm::Aes256Gcm => {
                HeaderProtectionKey::Aes(AesEcb::new(key.as_ref()).unwrap())
            }
            aead::Algorithm::ChaCha20Poly1305 => {
                HeaderProtectionKey::ChaCha20(Zeroizing::new(key.as_ref().try_into().unwrap()))
            }
        })
    }

    fn aead_key_len(&self) -> usize {
        self.packet_alg.key_len()
    }
}

#[cfg(test)]
mod tests {
    use rustls::crypto::cipher::{AeadKey, Iv};
    use rustls::error::Error;
    use rustls::quic::Algorithm;

    use super::{KeyBuilder, seal_failed};
    use crate::aead::{self, TAG_LEN};

    const ALGORITHMS: [aead::Algorithm; 3] = [
        aead::Algorithm::Aes128Gcm,
        aead::Algorithm::Aes256Gcm,
        aead::Algorithm::ChaCha20Poly1305,
    ];

    fn builder(packet_alg: aead::Algorithm) -> KeyBuilder {
        KeyBuilder {
            packet_alg,
            confidentiality_limit: 5,
            integrity_limit: 6,
        }
    }

    fn key(len: usize) -> AeadKey {
        match len {
            16 => AeadKey::from([0x22; 16]),
            _ => AeadKey::from([0x22; 32]),
        }
    }

    /// Header protection of each algorithm masks the low bits of the first
    /// byte (four of a long header, five of a short one) and as many bytes
    /// of the packet number as the first byte says, and unmasks what it
    /// masked. It refuses a sample of another length than its own, or a
    /// packet number longer than four bytes, and changes nothing then.
    #[test]
    fn header_protection() {
        for alg in ALGORITHMS {
            let builder = builder(alg);
            let hp = builder.header_protection_key(key(builder.aead_key_len()));
            let sample = [0x5a; 16];
            assert_eq!(hp.sample_len(), sample.len());
            // A long header with a 4-byte packet number, a short one with a
            // 1-byte packet number.
            for (first, bits, pn_len) in [(0xc3u8, 0x0f, 4), (0x40, 0x1f, 1)] {
                let plain = [1u8, 2, 3, 4];
                let (mut f, mut pn) = (first, plain);
                hp.encrypt_in_place(&sample, &mut f, &mut pn).unwrap();
                assert_eq!(f & !bits, first & !bits, "{alg:?}");
                assert_ne!(f, first, "{alg:?}");
                assert_eq!(pn[pn_len..], plain[pn_len..], "{alg:?}");
                assert_ne!(pn[..pn_len], plain[..pn_len], "{alg:?}");
                hp.decrypt_in_place(&sample, &mut f, &mut pn).unwrap();
                assert_eq!((f, pn), (first, plain), "{alg:?}");
            }
            let (mut f, mut pn) = (0xc3, [0u8; 5]);
            let too_long = hp.encrypt_in_place(&sample, &mut f, &mut pn);
            let short_sample = hp.encrypt_in_place(&sample[1..], &mut f, &mut pn[..4]);
            assert!(too_long.is_err() && short_sample.is_err(), "{alg:?}");
            assert_eq!((f, pn), (0xc3, [0; 5]), "{alg:?}");
        }
    }

    /// A packet key of each algorithm opens what it sealed, but not a payload
    /// shorter than a tag, and has its suite's limits.
    #[test]
    fn packet_key() {
        for alg in ALGORITHMS {
            let builder = builder(alg);
            let iv = Iv::new(&[0x55; 12]).unwrap();
            let pk = builder.packet_key(key(builder.aead_key_len()), iv);
            assert_eq!(pk.tag_len(), TAG_LEN);
            assert_eq!(pk.confidentiality_limit(), 5);
            assert_eq!(pk.integrity_limit(), 6);
            let mut sealed = *b"payload";
            let tag = pk
                .encrypt_in_place(9, b"header", &mut sealed, None)
                .unwrap();
            let mut sealed = [&sealed[..], tag.as_ref()].concat();
            let opened = pk.decrypt_in_place(9, b"header", &mut sealed, None);
            assert_eq!(opened.unwrap(), b"payload", "{alg:?}");
            let mut short = [0; TAG_LEN - 1];
            let short = pk.decrypt_in_place(9, b"header", &mut short, None);
            assert_eq!(short.err(), Some(Error::DecryptError), "{alg:?}");
        }
    }

    /// The error sealing's failure, which no test can cause, gives.
    #[test]
    fn seal_failure() {
        assert!(matches!(seal_failed(()), Error::EncryptError));
    }
}
