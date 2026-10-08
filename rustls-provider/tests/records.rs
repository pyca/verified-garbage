//! Every cipher suite seals a record the same from contiguous and from
//! fragmented plaintext (in more pieces than `AesGcm::encrypt` takes, too),
//! writing every byte of the record, and opens what it sealed.

use rustls::crypto::cipher::{
    AeadKey, EncodableVersion, InboundOpaque, Iv, OutboundPlain, Record, RecordDecrypter,
    RecordEncrypter,
};
use rustls::enums::{ContentType, ProtocolVersion};
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
    let mut out = vec![fill; enc.encrypted_payload_len(record.payload.len()) + 3];
    enc.encrypt(record, SEQ, &mut out).unwrap().payload.to_vec()
}

fn check(
    name: &str,
    version: ProtocolVersion,
    mut enc: impl FnMut() -> Box<dyn RecordEncrypter>,
    mut dec: impl FnMut() -> Box<dyn RecordDecrypter>,
) {
    let plain: Vec<u8> = (0..1000u32).map(|i| i as u8).collect();
    for len in [0, 1, 15, 16, 17, 100, 1000] {
        let plain = &plain[..len];
        let whole = seal(&mut *enc(), version, OutboundPlain::from(plain), 0x00);
        for n in [2, 3, 63, 64, 65, 200] {
            let pieces = chunked(plain, n);
            let fragmented = seal(&mut *enc(), version, OutboundPlain::new(&pieces), 0xff);
            assert_eq!(
                whole,
                fragmented,
                "{name}: {len} bytes in {} pieces",
                pieces.len()
            );
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
