//! SEC 1 conversions over brainpoolP512r1: the public keys of `ecdsa_brainpoolP512r1_sha512_p1363_test.json`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use verified_garbage::ecdh::BrainpoolP512r1;

public_keys!(
    brainpoolp512r1,
    BrainpoolP512r1,
    64,
    "ecdsa_brainpoolP512r1_sha512_p1363_test.json"
);
