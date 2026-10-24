//! SEC 1 conversions over secp256k1: the public keys of `ecdsa_secp256k1_sha256_p1363_test.json`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use verified_garbage::ecdh::Secp256k1;

public_keys!(
    secp256k1,
    Secp256k1,
    32,
    "ecdsa_secp256k1_sha256_p1363_test.json"
);
