//! HKDF-Expand from a pseudorandom key shorter than a digest, which RFC 5869
//! does not allow and the library refuses, but rustls's trait takes: it gives
//! a digest, as rustls's generic HKDF and aws-lc-rs's provider do, rather
//! than panic.

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
