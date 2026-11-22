//! Every suite's hash gives the same digest at once and incrementally, from
//! a context continued, copied or finished early.

use rustls::crypto::HashAlgorithm;
use rustls_verified_garbage as provider;

/// A message's digest is the same from `hash` and from a context it is fed
/// to in pieces; a context finished without being consumed, or copied, can
/// go on; the digest is as long as the hash says, and the algorithm is the
/// SHA-2 of that length.
#[test]
fn incremental() {
    let tls12 = provider::ALL_TLS12_CIPHER_SUITES.iter().map(|s| &s.common);
    let tls13 = provider::ALL_TLS13_CIPHER_SUITES.iter().map(|s| &s.common);
    for common in tls12.chain(tls13) {
        let (hash, name) = (common.hash_provider, format!("{:?}", common.suite));
        let message: Vec<u8> = (0..300u32).map(|i| i as u8).collect();
        let (head, tail) = message.split_at(100);
        let whole = hash.hash(&message);
        assert_eq!(whole.as_ref().len(), hash.output_len(), "{name}");
        let mut ctx = hash.start();
        ctx.update(head);
        let early = ctx.fork_finish();
        assert_eq!(early.as_ref(), hash.hash(head).as_ref(), "{name}");
        let mut copy = ctx.fork();
        ctx.update(tail);
        copy.update(tail);
        assert_eq!(copy.finish().as_ref(), whole.as_ref(), "{name}");
        assert_eq!(ctx.finish().as_ref(), whole.as_ref(), "{name}");
        let algorithm = match hash.output_len() {
            32 => HashAlgorithm::SHA256,
            _ => HashAlgorithm::SHA384,
        };
        assert_eq!(hash.algorithm(), algorithm, "{name}");
    }
}
