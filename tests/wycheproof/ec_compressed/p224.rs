//! SEC 1 conversions over P-224: the public keys of `ecdsa_secp224r1_sha224_p1363_test.json`,
//! and the compressed peers of `ecdh_secp224r1_ecpoint_test.json`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use verified_garbage::ecdh::P224;

public_keys!(p224, P224, 28, "ecdsa_secp224r1_sha224_p1363_test.json");
compressed_peers!(p224_peers, P224, 28, "ecdh_secp224r1_ecpoint_test.json");
