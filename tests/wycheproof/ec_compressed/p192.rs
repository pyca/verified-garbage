//! SEC 1 conversions over P-192: the public keys of `ecdsa_secp192r1_sha256_p1363_test.json`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use verified_garbage::ecdh::P192;

public_keys!(p192, P192, 24, "ecdsa_secp192r1_sha256_p1363_test.json");
