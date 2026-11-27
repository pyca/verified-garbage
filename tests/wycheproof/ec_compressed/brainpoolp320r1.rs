//! SEC 1 conversions over brainpoolP320r1: the public keys of `ecdsa_brainpoolP320r1_sha384_p1363_test.json`.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "powerpc64",
    target_arch = "riscv64"
))]

use verified_garbage::ec::BrainpoolP320r1;

public_keys!(
    brainpoolp320r1,
    BrainpoolP320r1,
    40,
    "ecdsa_brainpoolP320r1_sha384_p1363_test.json"
);
