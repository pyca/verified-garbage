//! QUIC packet and header protection (RFC 9001 §5).
//!
//! Only ChaCha20-Poly1305 supports QUIC: AES's header protection is
//! AES-ECB of one block (§5.4.3), which verified-garbage does not expose.

use alloc::boxed::Box;

use rustls::crypto::cipher::{AeadKey, Iv, Nonce};
use rustls::error::{ApiMisuse, Error};
use rustls::quic;
use verified_garbage::chacha20::ChaCha20;
use zeroize::Zeroizing;

use crate::aead::{self, TAG_LEN};

/// ChaCha20 header protection (RFC 9001 §5.4.4).
struct ChaCha20HeaderProtectionKey(Zeroizing<[u8; 32]>);

const SAMPLE_LEN: usize = 16;

impl ChaCha20HeaderProtectionKey {
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

        // The sample is the block counter (little-endian) and the nonce,
        // which is what `ChaCha20` takes as its 16-byte nonce.
        let mut mask = [0u8; 5];
        ChaCha20::new(&self.0, sample).apply_keystream(&mut mask);
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

impl quic::HeaderProtectionKey for ChaCha20HeaderProtectionKey {
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
            .map_err(|_| Error::EncryptError)?;
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
        match self.packet_alg {
            aead::Algorithm::ChaCha20Poly1305 => Box::new(ChaCha20HeaderProtectionKey(
                Zeroizing::new(key.as_ref().try_into().unwrap()),
            )),
            // `tls13` gives only ChaCha20-Poly1305 a `KeyBuilder`.
            _ => unreachable!(),
        }
    }

    fn aead_key_len(&self) -> usize {
        self.packet_alg.key_len()
    }
}
