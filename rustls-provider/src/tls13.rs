use alloc::boxed::Box;

use rustls::crypto::CipherSuite;
use rustls::crypto::cipher::{
    AeadKey, EncryptBuffer, InboundOpaque, Iv, Nonce, OutboundPlain, Record, RecordDecrypter,
    RecordEncrypter, Tls13AeadAlgorithm, UnsupportedOperationError, make_tls13_aad,
};
use rustls::crypto::tls13::HkdfUsingHmac;
use rustls::enums::ContentType;
use rustls::error::Error;
use rustls::version::TLS13_VERSION;
use rustls::{CipherSuiteCommon, ConnectionTrafficSecrets, Tls13CipherSuite};

use crate::aead::{self, TAG_LEN};

/// The TLS1.3 cipher suite configuration that an application should use by default.
pub static DEFAULT_TLS13_CIPHER_SUITES: &[&Tls13CipherSuite] = ALL_TLS13_CIPHER_SUITES;

/// A list of all the TLS1.3 cipher suites supported by this provider.
pub static ALL_TLS13_CIPHER_SUITES: &[&Tls13CipherSuite] = &[
    TLS13_AES_128_GCM_SHA256,
    TLS13_AES_256_GCM_SHA384,
    TLS13_CHACHA20_POLY1305_SHA256,
];

/// The TLS1.3 ciphersuite TLS_CHACHA20_POLY1305_SHA256
pub static TLS13_CHACHA20_POLY1305_SHA256: &Tls13CipherSuite = &Tls13CipherSuite {
    common: CipherSuiteCommon {
        suite: CipherSuite::TLS13_CHACHA20_POLY1305_SHA256,
        hash_provider: &super::hash::SHA256,
        // ref: <https://www.ietf.org/archive/id/draft-irtf-cfrg-aead-limits-08.html#section-5.2.1>
        confidentiality_limit: u64::MAX,
    },
    protocol_version: TLS13_VERSION,
    hkdf_provider: &HkdfUsingHmac(&super::hmac::HMAC_SHA256),
    aead_alg: &Tls13Aead(aead::Algorithm::ChaCha20Poly1305),
    quic: Some(&super::quic::KeyBuilder {
        packet_alg: aead::Algorithm::ChaCha20Poly1305,
        // ref: <https://datatracker.ietf.org/doc/html/rfc9001#section-6.6>
        confidentiality_limit: u64::MAX,
        // ref: <https://datatracker.ietf.org/doc/html/rfc9001#section-6.6>
        integrity_limit: 1 << 36,
    }),
};

/// The TLS1.3 ciphersuite TLS_AES_256_GCM_SHA384
pub static TLS13_AES_256_GCM_SHA384: &Tls13CipherSuite = &Tls13CipherSuite {
    common: CipherSuiteCommon {
        suite: CipherSuite::TLS13_AES_256_GCM_SHA384,
        hash_provider: &super::hash::SHA384,
        confidentiality_limit: 1 << 24,
    },
    protocol_version: TLS13_VERSION,
    hkdf_provider: &HkdfUsingHmac(&super::hmac::HMAC_SHA384),
    aead_alg: &Tls13Aead(aead::Algorithm::Aes256Gcm),
    // QUIC's header protection for AES suites is AES-ECB of one block
    // (RFC 9001 §5.4.3), which verified-garbage does not expose.
    quic: None,
};

/// The TLS1.3 ciphersuite TLS_AES_128_GCM_SHA256
pub static TLS13_AES_128_GCM_SHA256: &Tls13CipherSuite = &Tls13CipherSuite {
    common: CipherSuiteCommon {
        suite: CipherSuite::TLS13_AES_128_GCM_SHA256,
        hash_provider: &super::hash::SHA256,
        confidentiality_limit: 1 << 24,
    },
    protocol_version: TLS13_VERSION,
    hkdf_provider: &HkdfUsingHmac(&super::hmac::HMAC_SHA256),
    aead_alg: &Tls13Aead(aead::Algorithm::Aes128Gcm),
    // QUIC's header protection for AES suites is AES-ECB of one block
    // (RFC 9001 §5.4.3), which verified-garbage does not expose.
    quic: None,
};

struct Tls13Aead(aead::Algorithm);

impl Tls13AeadAlgorithm for Tls13Aead {
    fn encrypter(&self, key: AeadKey, iv: Iv) -> Box<dyn RecordEncrypter> {
        Box::new(Tls13RecordEncrypter {
            key: self.0.key(key.as_ref()),
            iv,
        })
    }

    fn decrypter(&self, key: AeadKey, iv: Iv) -> Box<dyn RecordDecrypter> {
        Box::new(Tls13RecordDecrypter {
            key: self.0.key(key.as_ref()),
            iv,
        })
    }

    fn key_len(&self) -> usize {
        self.0.key_len()
    }

    fn extract_keys(
        &self,
        key: AeadKey,
        iv: Iv,
    ) -> Result<ConnectionTrafficSecrets, UnsupportedOperationError> {
        Ok(match self.0 {
            aead::Algorithm::Aes128Gcm => ConnectionTrafficSecrets::Aes128Gcm { key, iv },
            aead::Algorithm::Aes256Gcm => ConnectionTrafficSecrets::Aes256Gcm { key, iv },
            aead::Algorithm::ChaCha20Poly1305 => {
                ConnectionTrafficSecrets::Chacha20Poly1305 { key, iv }
            }
        })
    }
}

struct Tls13RecordEncrypter {
    key: aead::Key,
    iv: Iv,
}

impl RecordEncrypter for Tls13RecordEncrypter {
    fn encrypt<'a>(
        &mut self,
        msg: Record<OutboundPlain<'_>>,
        seq: u64,
        out: &'a mut [u8],
    ) -> Result<Record<&'a [u8]>, Error> {
        let total_len = self.encrypted_payload_len(msg.payload.len());
        let mut payload = EncryptBuffer::new(out, total_len)?;

        let typ = ContentType::ApplicationData;
        let nonce = Nonce::new(&self.iv, seq).to_array()?;
        let aad = make_tls13_aad(typ, msg.version.encode(), total_len);
        // The plaintext is gathered into `out`, then encrypted there.
        payload.extend_from_chunks(&msg.payload);
        payload.extend_from_slice(&msg.typ.to_array());

        let tag = self
            .key
            .seal(&nonce, &aad, payload.as_mut())
            .map_err(|_| Error::EncryptError)?;
        payload.extend_from_slice(&tag);

        Ok(Record {
            typ,
            version: msg.version,
            payload: payload.into_written(),
        })
    }

    fn encrypted_payload_len(&self, payload_len: usize) -> usize {
        payload_len + 1 + TAG_LEN
    }
}

struct Tls13RecordDecrypter {
    key: aead::Key,
    iv: Iv,
}

impl RecordDecrypter for Tls13RecordDecrypter {
    fn decrypt<'a>(
        &mut self,
        mut record: Record<InboundOpaque<'a>>,
        seq: u64,
    ) -> Result<Record<&'a [u8]>, Error> {
        let payload = &mut record.payload;
        if payload.len() < TAG_LEN {
            return Err(Error::DecryptError);
        }

        let nonce = Nonce::new(&self.iv, seq).to_array()?;
        let aad = make_tls13_aad(record.typ, record.version.version(), payload.len());
        let plain_len = self
            .key
            .open(&nonce, &aad, payload)
            .map_err(|_| Error::DecryptError)?;

        payload.truncate(plain_len);
        record.into_tls13_unpadded_record()
    }
}
