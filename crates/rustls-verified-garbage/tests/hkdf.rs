//! HKDF-Expand from a pseudorandom key shorter than a digest, which RFC 5869
//! does not allow and the library refuses, but rustls's trait takes: it gives
//! a digest, as rustls's generic HKDF and aws-lc-rs's provider do, rather
//! than panic. And from an `info` longer than any TLS 1.3 label, and what
//! each of the HKDF's functions gives, checked against the others.

use rustls::crypto::tls13::{HkdfExpander, OkmBlock};
use rustls_verified_garbage as provider;

#[test]
fn short_prk() {
    for suite in provider::ALL_TLS13_CIPHER_SUITES {
        let hkdf = suite.hkdf_provider;
        let len = suite.common.hash_provider.output_len();
        for prk_len in [1, len - 1, len] {
            let expander = hkdf.expander_for_okm(&OkmBlock::new(&vec![5u8; prk_len]));
            let block = expander.expand_block(&[b"label"]);
            assert_eq!(
                block.as_ref().len(),
                len,
                "{:?}: {prk_len}",
                suite.common.suite
            );
        }
    }
}

/// HKDF-Expand of an `info` longer than any TLS 1.3 label gives the same
/// from `info` whole and in pieces, and not what its prefix gives.
#[test]
fn long_info() {
    for suite in provider::ALL_TLS13_CIPHER_SUITES {
        let len = suite.common.hash_provider.output_len();
        let expander = suite
            .hkdf_provider
            .expander_for_okm(&OkmBlock::new(&vec![5u8; len]));
        let info: Vec<u8> = (0..1000u32).map(|i| i as u8).collect();
        let expand = |info: &[&[u8]]| {
            let mut out = [0u8; 100];
            expander.expand_slice(info, &mut out).unwrap();
            out
        };
        let pieces: Vec<&[u8]> = info.chunks(7).collect();
        let name = format!("{:?}", suite.common.suite);
        assert_eq!(expand(&[&info]), expand(&pieces), "{name}");
        assert_ne!(expand(&[&info]), expand(&[&info[..999]]), "{name}");
    }
}

/// HKDF-Extract is HMAC keyed with the salt (RFC 5869 §2.2), and the salt
/// is a digest's length of zeros when absent, as is the secret
/// `extract_from_zero_ikm` takes: each extraction expands as the expander
/// of the HMAC tag does. Expanding more than 255 digests is refused.
#[test]
fn extract() {
    for suite in provider::ALL_TLS13_CIPHER_SUITES {
        let hkdf = suite.hkdf_provider;
        let len = suite.common.hash_provider.output_len();
        let name = format!("{:?}", suite.common.suite);
        let expand = |expander: &dyn HkdfExpander| {
            assert_eq!(expander.hash_len(), len, "{name}");
            expander.expand_block(&[b"label"])
        };
        let (salt, zeros) = (b"salt", vec![0u8; len]);
        let prk = hkdf.hmac_sign(&OkmBlock::new(salt), b"secret");
        let from_prk = expand(&*hkdf.expander_for_okm(&OkmBlock::new(prk.as_ref())));
        let from_secret = expand(&*hkdf.extract_from_secret(Some(salt), b"secret"));
        assert_eq!(from_secret.as_ref(), from_prk.as_ref(), "{name}");
        let no_salt = expand(&*hkdf.extract_from_secret(None, b"secret"));
        let zero_salt = expand(&*hkdf.extract_from_secret(Some(&zeros), b"secret"));
        assert_eq!(no_salt.as_ref(), zero_salt.as_ref(), "{name}");
        let zero_ikm = expand(&*hkdf.extract_from_zero_ikm(Some(salt)));
        let zero_secret = expand(&*hkdf.extract_from_secret(Some(salt), &zeros));
        assert_eq!(zero_ikm.as_ref(), zero_secret.as_ref(), "{name}");
        let mut too_long = vec![0u8; 255 * len + 1];
        let expander = hkdf.extract_from_secret(None, b"secret");
        assert!(
            expander.expand_slice(&[b"label"], &mut too_long).is_err(),
            "{name}"
        );
    }
}
