use alloc::boxed::Box;

use rustls::crypto::cipher::{
    AeadKey, InboundOpaque, Iv, KeyBlockShape, NONCE_LEN, Nonce, OutboundPlain, Record,
    RecordDecrypter, RecordEncrypter, Tls12AeadAlgorithm, UnsupportedOperationError,
    make_tls12_aad,
};
use rustls::crypto::kx::KeyExchangeAlgorithm;
use rustls::crypto::tls12::PrfUsingHmac;
use rustls::crypto::{CipherSuite, SignatureScheme};
use rustls::error::Error;
use rustls::version::TLS12_VERSION;
use rustls::{CipherSuiteCommon, ConnectionTrafficSecrets, Tls12CipherSuite};

use crate::aead::{self, TAG_LEN};

/// The TLS1.2 cipher suite configuration that an application should use by default.
pub static DEFAULT_TLS12_CIPHER_SUITES: &[&Tls12CipherSuite] = ALL_TLS12_CIPHER_SUITES;

/// A list of all the TLS1.2 cipher suites supported by this provider.
pub static ALL_TLS12_CIPHER_SUITES: &[&Tls12CipherSuite] = &[
    TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256,
    TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384,
    TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256,
    TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256,
    TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384,
    TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256,
];

/// The TLS1.2 ciphersuite TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256.
pub static TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256: &Tls12CipherSuite = &Tls12CipherSuite {
    common: CipherSuiteCommon {
        suite: CipherSuite::TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256,
        hash_provider: &super::hash::SHA256,
        confidentiality_limit: u64::MAX,
    },
    protocol_version: TLS12_VERSION,
    kx: KeyExchangeAlgorithm::ECDHE,
    sign: TLS12_ECDSA_SCHEMES,
    aead_alg: &ChaCha20Poly1305,
    prf_provider: &PrfUsingHmac(&super::hmac::HMAC_SHA256),
};

/// The TLS1.2 ciphersuite TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256
pub static TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256: &Tls12CipherSuite = &Tls12CipherSuite {
    common: CipherSuiteCommon {
        suite: CipherSuite::TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256,
        hash_provider: &super::hash::SHA256,
        confidentiality_limit: u64::MAX,
    },
    protocol_version: TLS12_VERSION,
    kx: KeyExchangeAlgorithm::ECDHE,
    sign: TLS12_RSA_SCHEMES,
    aead_alg: &ChaCha20Poly1305,
    prf_provider: &PrfUsingHmac(&super::hmac::HMAC_SHA256),
};

/// The TLS1.2 ciphersuite TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256
pub static TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256: &Tls12CipherSuite = &Tls12CipherSuite {
    common: CipherSuiteCommon {
        suite: CipherSuite::TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256,
        hash_provider: &super::hash::SHA256,
        confidentiality_limit: 1 << 24,
    },
    protocol_version: TLS12_VERSION,
    kx: KeyExchangeAlgorithm::ECDHE,
    sign: TLS12_RSA_SCHEMES,
    aead_alg: &AES128_GCM,
    prf_provider: &PrfUsingHmac(&super::hmac::HMAC_SHA256),
};

/// The TLS1.2 ciphersuite TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384
pub static TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384: &Tls12CipherSuite = &Tls12CipherSuite {
    common: CipherSuiteCommon {
        suite: CipherSuite::TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384,
        hash_provider: &super::hash::SHA384,
        confidentiality_limit: 1 << 24,
    },
    protocol_version: TLS12_VERSION,
    kx: KeyExchangeAlgorithm::ECDHE,
    sign: TLS12_RSA_SCHEMES,
    aead_alg: &AES256_GCM,
    prf_provider: &PrfUsingHmac(&super::hmac::HMAC_SHA384),
};

/// The TLS1.2 ciphersuite TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256
pub static TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256: &Tls12CipherSuite = &Tls12CipherSuite {
    common: CipherSuiteCommon {
        suite: CipherSuite::TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256,
        hash_provider: &super::hash::SHA256,
        confidentiality_limit: 1 << 24,
    },
    protocol_version: TLS12_VERSION,
    kx: KeyExchangeAlgorithm::ECDHE,
    sign: TLS12_ECDSA_SCHEMES,
    aead_alg: &AES128_GCM,
    prf_provider: &PrfUsingHmac(&super::hmac::HMAC_SHA256),
};

/// The TLS1.2 ciphersuite TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384
pub static TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384: &Tls12CipherSuite = &Tls12CipherSuite {
    common: CipherSuiteCommon {
        suite: CipherSuite::TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384,
        hash_provider: &super::hash::SHA384,
        confidentiality_limit: 1 << 24,
    },
    protocol_version: TLS12_VERSION,
    kx: KeyExchangeAlgorithm::ECDHE,
    sign: TLS12_ECDSA_SCHEMES,
    aead_alg: &AES256_GCM,
    prf_provider: &PrfUsingHmac(&super::hmac::HMAC_SHA384),
};

static TLS12_ECDSA_SCHEMES: &[SignatureScheme] = &[
    SignatureScheme::ED25519,
    SignatureScheme::ECDSA_NISTP521_SHA512,
    SignatureScheme::ECDSA_NISTP384_SHA384,
    SignatureScheme::ECDSA_NISTP256_SHA256,
];

static TLS12_RSA_SCHEMES: &[SignatureScheme] = &[
    SignatureScheme::RSA_PSS_SHA512,
    SignatureScheme::RSA_PSS_SHA384,
    SignatureScheme::RSA_PSS_SHA256,
    SignatureScheme::RSA_PKCS1_SHA512,
    SignatureScheme::RSA_PKCS1_SHA384,
    SignatureScheme::RSA_PKCS1_SHA256,
];

static AES128_GCM: GcmAlgorithm = GcmAlgorithm(aead::Algorithm::Aes128Gcm);
static AES256_GCM: GcmAlgorithm = GcmAlgorithm(aead::Algorithm::Aes256Gcm);

struct GcmAlgorithm(aead::Algorithm);

impl Tls12AeadAlgorithm for GcmAlgorithm {
    fn decrypter(&self, dec_key: AeadKey, dec_iv: &[u8]) -> Box<dyn RecordDecrypter> {
        Box::new(GcmRecordDecrypter {
            key: self.0.key(dec_key.as_ref()),
            salt: dec_iv
                .try_into()
                .expect("IV length validated by key_block_shape"),
        })
    }

    fn encrypter(
        &self,
        enc_key: AeadKey,
        write_iv: &[u8],
        explicit: &[u8],
    ) -> Box<dyn RecordEncrypter> {
        Box::new(GcmRecordEncrypter {
            key: self.0.key(enc_key.as_ref()),
            iv: gcm_iv(write_iv, explicit),
        })
    }

    fn key_block_shape(&self) -> KeyBlockShape {
        KeyBlockShape {
            enc_key_len: self.0.key_len(),
            fixed_iv_len: 4,
            explicit_nonce_len: 8,
        }
    }

    fn extract_keys(
        &self,
        key: AeadKey,
        write_iv: &[u8],
        explicit: &[u8],
    ) -> Result<ConnectionTrafficSecrets, UnsupportedOperationError> {
        let iv = gcm_iv(write_iv, explicit);
        Ok(match self.0 {
            aead::Algorithm::Aes128Gcm => ConnectionTrafficSecrets::Aes128Gcm { key, iv },
            _ => ConnectionTrafficSecrets::Aes256Gcm { key, iv },
        })
    }
}

struct ChaCha20Poly1305;

impl Tls12AeadAlgorithm for ChaCha20Poly1305 {
    fn decrypter(&self, dec_key: AeadKey, iv: &[u8]) -> Box<dyn RecordDecrypter> {
        Box::new(ChaCha20Poly1305RecordDecrypter {
            key: aead::Algorithm::ChaCha20Poly1305.key(dec_key.as_ref()),
            offset: Iv::new(iv).expect("IV length validated by key_block_shape"),
        })
    }

    fn encrypter(&self, enc_key: AeadKey, enc_iv: &[u8], _: &[u8]) -> Box<dyn RecordEncrypter> {
        Box::new(ChaCha20Poly1305RecordEncrypter {
            key: aead::Algorithm::ChaCha20Poly1305.key(enc_key.as_ref()),
            offset: Iv::new(enc_iv).expect("IV length validated by key_block_shape"),
        })
    }

    fn key_block_shape(&self) -> KeyBlockShape {
        KeyBlockShape {
            enc_key_len: 32,
            fixed_iv_len: 12,
            explicit_nonce_len: 0,
        }
    }

    fn extract_keys(
        &self,
        key: AeadKey,
        iv: &[u8],
        _explicit: &[u8],
    ) -> Result<ConnectionTrafficSecrets, UnsupportedOperationError> {
        Ok(ConnectionTrafficSecrets::Chacha20Poly1305 {
            key,
            iv: Iv::new(iv).expect("IV length validated by key_block_shape"),
        })
    }
}

/// A `RecordEncrypter` for AES-GCM AEAD ciphersuites. TLS 1.2 only.
struct GcmRecordEncrypter {
    key: aead::Key,
    iv: Iv,
}

/// A `RecordDecrypter` for AES-GCM AEAD ciphersuites.  TLS1.2 only.
struct GcmRecordDecrypter {
    key: aead::Key,
    salt: [u8; 4],
}

const GCM_EXPLICIT_NONCE_LEN: usize = 8;
const GCM_OVERHEAD: usize = GCM_EXPLICIT_NONCE_LEN + TAG_LEN;

impl RecordDecrypter for GcmRecordDecrypter {
    fn decrypt<'a>(
        &mut self,
        mut record: Record<InboundOpaque<'a>>,
        seq: u64,
    ) -> Result<Record<&'a [u8]>, Error> {
        let payload = &mut record.payload;
        if payload.len() < GCM_OVERHEAD {
            return Err(Error::DecryptError);
        }

        let mut nonce = [0u8; NONCE_LEN];
        nonce[..4].copy_from_slice(&self.salt);
        nonce[4..].copy_from_slice(&payload[..GCM_EXPLICIT_NONCE_LEN]);

        let aad = make_tls12_aad(
            seq,
            record.typ,
            record.version.version(),
            payload.len() - GCM_OVERHEAD,
        );

        let plain_len = self
            .key
            .open(&nonce, &aad, &mut payload[GCM_EXPLICIT_NONCE_LEN..])
            .map_err(|_| Error::DecryptError)?;

        if plain_len > MAX_FRAGMENT_LEN {
            return Err(Error::PeerSentOversizedRecord);
        }

        Ok(record
            .into_plain_record_range(GCM_EXPLICIT_NONCE_LEN..GCM_EXPLICIT_NONCE_LEN + plain_len))
    }
}

impl RecordEncrypter for GcmRecordEncrypter {
    fn encrypt<'a>(
        &mut self,
        record: Record<OutboundPlain<'_>>,
        seq: u64,
        out: &'a mut [u8],
    ) -> Result<Record<&'a [u8]>, Error> {
        let total_len = self.encrypted_payload_len(record.payload.len());
        let out = aead::record_region(out, total_len)?;

        let nonce: [u8; NONCE_LEN] = Nonce::new(&self.iv, seq).to_array()?;
        let aad = make_tls12_aad(
            seq,
            record.typ,
            record.version.encode(),
            record.payload.len(),
        );
        // The explicit nonce, then the ciphertext, encrypted from the
        // payload where it is, then the tag.
        let (explicit, rest) = out.split_at_mut(GCM_EXPLICIT_NONCE_LEN);
        explicit.copy_from_slice(&nonce[4..]);
        let (ciphertext, tag_out) = rest.split_at_mut(record.payload.len());
        let tag = self
            .key
            .seal_to(&nonce, &aad, &record.payload, &[], ciphertext)
            .map_err(|_| Error::EncryptError)?;
        tag_out.copy_from_slice(&tag);

        Ok(Record {
            typ: record.typ,
            version: record.version,
            payload: &*out,
        })
    }

    fn encrypted_payload_len(&self, payload_len: usize) -> usize {
        payload_len + GCM_OVERHEAD
    }
}

/// The RFC 7905/RFC 7539 ChaCha20Poly1305 construction.
/// This implementation does the AAD construction required in TLS1.2.
struct ChaCha20Poly1305RecordEncrypter {
    key: aead::Key,
    offset: Iv,
}

/// The RFC 7905/RFC 7539 ChaCha20Poly1305 construction.
/// This implementation does the AAD construction required in TLS1.2.
struct ChaCha20Poly1305RecordDecrypter {
    key: aead::Key,
    offset: Iv,
}

impl RecordDecrypter for ChaCha20Poly1305RecordDecrypter {
    fn decrypt<'a>(
        &mut self,
        mut record: Record<InboundOpaque<'a>>,
        seq: u64,
    ) -> Result<Record<&'a [u8]>, Error> {
        let payload = &mut record.payload;
        if payload.len() < TAG_LEN {
            return Err(Error::DecryptError);
        }

        let nonce = Nonce::new(&self.offset, seq).to_array()?;
        let aad = make_tls12_aad(
            seq,
            record.typ,
            record.version.version(),
            payload.len() - TAG_LEN,
        );

        let plain_len = self
            .key
            .open(&nonce, &aad, payload)
            .map_err(|_| Error::DecryptError)?;

        if plain_len > MAX_FRAGMENT_LEN {
            return Err(Error::PeerSentOversizedRecord);
        }

        payload.truncate(plain_len);
        Ok(record.into_plain_record())
    }
}

impl RecordEncrypter for ChaCha20Poly1305RecordEncrypter {
    fn encrypt<'a>(
        &mut self,
        record: Record<OutboundPlain<'_>>,
        seq: u64,
        out: &'a mut [u8],
    ) -> Result<Record<&'a [u8]>, Error> {
        let total_len = self.encrypted_payload_len(record.payload.len());
        let out = aead::record_region(out, total_len)?;

        let nonce = Nonce::new(&self.offset, seq).to_array()?;
        let aad = make_tls12_aad(
            seq,
            record.typ,
            record.version.encode(),
            record.payload.len(),
        );
        let (ciphertext, tag_out) = out.split_at_mut(record.payload.len());
        let tag = self
            .key
            .seal_to(&nonce, &aad, &record.payload, &[], ciphertext)
            .map_err(|_| Error::EncryptError)?;
        tag_out.copy_from_slice(&tag);

        Ok(Record {
            typ: record.typ,
            version: record.version,
            payload: &*out,
        })
    }

    fn encrypted_payload_len(&self, payload_len: usize) -> usize {
        payload_len + TAG_LEN
    }
}

fn gcm_iv(write_iv: &[u8], explicit: &[u8]) -> Iv {
    debug_assert_eq!(write_iv.len(), 4);
    debug_assert_eq!(explicit.len(), 8);

    // The GCM nonce is constructed from a 32-bit 'salt' derived
    // from the master-secret, and a 64-bit explicit part,
    // with no specified construction.
    //
    // We use the same construction as TLS1.3/ChaCha20Poly1305:
    // a starting point extracted from the key block, xored with
    // the sequence number.
    let mut iv = [0; NONCE_LEN];
    iv[..4].copy_from_slice(write_iv);
    iv[4..].copy_from_slice(explicit);

    Iv::new(&iv).expect("IV length is NONCE_LEN, which is within MAX_LEN")
}

const MAX_FRAGMENT_LEN: usize = 16384;
