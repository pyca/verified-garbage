//! SEC 1 conversions over P-521: the public keys of `ecdsa_secp521r1_sha512_p1363_test.json`,
//! and the compressed peers of `ecdh_secp521r1_ecpoint_test.json`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use verified_garbage::ecdh::P521;

public_keys!(p521, P521, 66, "ecdsa_secp521r1_sha512_p1363_test.json");
compressed_peers!(p521_peers, P521, 66, "ecdh_secp521r1_ecpoint_test.json");
