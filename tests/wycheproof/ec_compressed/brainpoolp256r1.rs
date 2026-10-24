//! SEC 1 conversions over brainpoolP256r1: the public keys of `ecdsa_brainpoolP256r1_sha256_p1363_test.json`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use verified_garbage::ecdh::BrainpoolP256r1;

public_keys!(
    brainpoolp256r1,
    BrainpoolP256r1,
    32,
    "ecdsa_brainpoolP256r1_sha256_p1363_test.json"
);
