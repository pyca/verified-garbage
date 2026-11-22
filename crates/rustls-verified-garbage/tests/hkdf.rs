//! HKDF-Expand from a pseudorandom key shorter than a digest, which RFC 5869
//! does not allow and the library refuses, but rustls's trait takes: it gives
//! a digest, as rustls's generic HKDF and aws-lc-rs's provider do, rather
//! than panic. And from an `info` longer than any TLS 1.3 label.

use rustls::crypto::tls13::OkmBlock;
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
