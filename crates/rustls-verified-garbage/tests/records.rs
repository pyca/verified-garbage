//! Every cipher suite seals a record the same from contiguous and from
//! fragmented plaintext, appending the whole record (its header too) after
//! what the output already holds, and opens what it sealed.

use rustls::ConnectionTrafficSecrets;
use rustls::crypto::cipher::{
    AeadKey, EncodableVersion, InboundOpaque, Iv, OutboundPlain, Record, RecordDecrypter,
    RecordEncrypter,
};
use rustls::enums::{ContentType, ProtocolVersion};
use rustls::error::Error;
use rustls_verified_garbage as provider;

const SEQ: u64 = 7;

fn key(len: usize) -> AeadKey {
    match len {
        16 => AeadKey::from([0x22; 16]),
        _ => AeadKey::from([0x22; 32]),
    }
}

/// The plaintext in contiguous form and in `n` pieces.
fn chunked(plain: &[u8], n: usize) -> Vec<&[u8]> {
    let size = plain.len().div_ceil(n).max(1);
    plain.chunks(size).collect()
}

fn seal(
    enc: &mut dyn RecordEncrypter,
    version: ProtocolVersion,
    plain: OutboundPlain<'_>,
    fill: u8,
) -> Vec<u8> {
    let record = Record::new(
        ContentType::ApplicationData,
        EncodableVersion::Legacy(version),
        plain,
    );
    let len = enc.encrypted_payload_len(record.payload.len());
    // What the output already holds, which the record goes after.
    let mut out = vec![fill; 3];
    enc.encrypt(record, SEQ, &mut out).unwrap();
    assert_eq!(out.len(), 3 + 5 + len);
    assert_eq!(out[..3], [fill; 3]);
    // The header: the record's type (application data, the plaintext's
    // in TLS 1.2 and every record's in TLS 1.3), its version and the
    // payload's length.
    let [hi, lo] = u16::try_from(len).unwrap().to_be_bytes();
    let [vhi, vlo] = EncodableVersion::Legacy(version).encode().to_array();
    assert_eq!(
        out[3..8],
        [u8::from(ContentType::ApplicationData), vhi, vlo, hi, lo]
    );
    out[8..].to_vec()
}

fn check(
    name: &str,
    version: ProtocolVersion,
    mut enc: impl FnMut() -> Box<dyn RecordEncrypter>,
    mut dec: impl FnMut() -> Box<dyn RecordDecrypter>,
) {
    let plain: Vec<u8> = (0..1000u32).map(|i| i as u8).collect();
    for len in [0, 1, 15, 16, 17, 100, 510, 511, 512, 1000] {
        let plain = &plain[..len];
        let whole = seal(&mut *enc(), version, OutboundPlain::from(plain), 0x00);
        for n in [2, 3, 63, 64, 65, 200] {
            let pieces = chunked(plain, n);
            let count = pieces.len();
            let fragmented = seal(&mut *enc(), version, OutboundPlain::new(&pieces), 0xff);
            assert_eq!(whole, fragmented, "{name}: {len} bytes in {count} pieces");
        }
        let mut sealed = whole.clone();
        let record = Record::new(
            ContentType::ApplicationData,
            EncodableVersion::Legacy(ProtocolVersion::TLSv1_2),
            InboundOpaque(&mut sealed),
        );
        let opened = dec().decrypt(record, SEQ).unwrap();
        assert_eq!(opened.typ, ContentType::ApplicationData, "{name}");
        assert_eq!(opened.payload, plain, "{name}: {len} bytes");
    }
}

#[test]
fn tls13_records() {
    for suite in provider::ALL_TLS13_CIPHER_SUITES {
        let alg = suite.aead_alg;
        let iv = || Iv::new(&[0x55; 12]).unwrap();
        check(
            &format!("{:?}", suite.common.suite),
            ProtocolVersion::TLSv1_3,
            || alg.encrypter(key(alg.key_len()), iv()),
            || alg.decrypter(key(alg.key_len()), iv()),
        );
    }
}

#[test]
fn tls12_records() {
    for suite in provider::ALL_TLS12_CIPHER_SUITES {
        let alg = suite.aead_alg;
        let shape = alg.key_block_shape();
        let iv = vec![0x55; shape.fixed_iv_len];
        let explicit = vec![0x66; shape.explicit_nonce_len];
        check(
            &format!("{:?}", suite.common.suite),
            ProtocolVersion::TLSv1_2,
            || alg.encrypter(key(shape.enc_key_len), &iv, &explicit),
            || alg.decrypter(key(shape.enc_key_len), &iv),
        );
    }
}

/// No TLS 1.2 cipher suite opens a record too short for its explicit nonce
/// and tag, or one whose plaintext is longer than a record's may be (2^14
/// bytes), though it sealed it.
#[test]
fn tls12_bad_records() {
    for suite in provider::ALL_TLS12_CIPHER_SUITES {
        let alg = suite.aead_alg;
        let shape = alg.key_block_shape();
        let iv = vec![0x55; shape.fixed_iv_len];
        let explicit = vec![0x66; shape.explicit_nonce_len];
        let mut enc = alg.encrypter(key(shape.enc_key_len), &iv, &explicit);
        let open = |mut payload: Vec<u8>| {
            let record = Record::new(
                ContentType::ApplicationData,
                EncodableVersion::Legacy(ProtocolVersion::TLSv1_2),
                InboundOpaque(&mut payload),
            );
            let mut dec = alg.decrypter(key(shape.enc_key_len), &iv);
            dec.decrypt(record, SEQ).err()
        };
        let name = format!("{:?}", suite.common.suite);
        let short = vec![0; enc.encrypted_payload_len(0) - 1];
        assert_eq!(open(short), Some(Error::DecryptError), "{name}");
        let plain = vec![0; (1 << 14) + 1];
        let oversized = seal(
            &mut *enc,
            ProtocolVersion::TLSv1_2,
            OutboundPlain::from(&plain[..]),
            0,
        );
        let err = Some(Error::PeerSentOversizedRecord);
        assert_eq!(open(oversized), err, "{name}");
    }
}

/// Whether `secrets` are of the AEAD the suite `suite` names, with the key
/// `key` and the IV `iv`.
fn holds(secrets: &ConnectionTrafficSecrets, suite: &str, key: &[u8], iv: &[u8]) -> bool {
    use ConnectionTrafficSecrets as S;
    let same = |k: &AeadKey, v: &Iv| k.as_ref() == key && v.as_ref() == iv;
    matches!(secrets, S::Aes128Gcm { key, iv } if suite.contains("AES_128_GCM") && same(key, iv))
        || matches!(secrets, S::Aes256Gcm { key, iv } if suite.contains("AES_256_GCM") && same(key, iv))
        || matches!(secrets, S::Chacha20Poly1305 { key, iv } if suite.contains("CHACHA20") && same(key, iv))
}

/// Each TLS 1.3 suite gives its AEAD's traffic secrets with the key and IV
/// it is given, and opens no record shorter than a tag.
#[test]
fn tls13_secrets() {
    for suite in provider::ALL_TLS13_CIPHER_SUITES {
        let alg = suite.aead_alg;
        let name = format!("{:?}", suite.common.suite);
        let iv = Iv::new(&[0x55; 12]).unwrap();
        let secrets = alg.extract_keys(key(alg.key_len()), iv).unwrap();
        let k = key(alg.key_len());
        assert!(holds(&secrets, &name, k.as_ref(), &[0x55; 12]), "{name}");
        let mut short = [0u8; 15];
        let record = Record::new(
            ContentType::ApplicationData,
            EncodableVersion::Legacy(ProtocolVersion::TLSv1_2),
            InboundOpaque(&mut short),
        );
        let mut dec = alg.decrypter(key(alg.key_len()), Iv::new(&[0x55; 12]).unwrap());
        assert_eq!(
            dec.decrypt(record, SEQ).err(),
            Some(Error::DecryptError),
            "{name}"
        );
    }
}

/// Each TLS 1.2 suite gives its AEAD's traffic secrets with the key it is
/// given and the IV of its nonces: the fixed IV, followed by the explicit
/// nonce if it has one.
#[test]
fn tls12_secrets() {
    for suite in provider::ALL_TLS12_CIPHER_SUITES {
        let alg = suite.aead_alg;
        let name = format!("{:?}", suite.common.suite);
        let shape = alg.key_block_shape();
        let iv = vec![0x55; shape.fixed_iv_len];
        let explicit = vec![0x66; shape.explicit_nonce_len];
        let secrets = alg
            .extract_keys(key(shape.enc_key_len), &iv, &explicit)
            .unwrap();
        let k = key(shape.enc_key_len);
        let nonce_iv = [&iv[..], &explicit[..]].concat();
        assert!(holds(&secrets, &name, k.as_ref(), &nonce_iv), "{name}");
    }
}
