//! SEC 1 conversions over P-256: the public keys of `ecdsa_secp256r1_sha256_p1363_test.json`,
//! and the compressed peers of `ecdh_secp256r1_ecpoint_test.json`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::ecdh::P256;

public_keys!(p256, P256, 32, "ecdsa_secp256r1_sha256_p1363_test.json");
compressed_peers!(p256_peers, P256, 32, "ecdh_secp256r1_ecpoint_test.json");
