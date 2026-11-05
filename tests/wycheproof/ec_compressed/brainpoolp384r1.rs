//! SEC 1 conversions over brainpoolP384r1: the public keys of `ecdsa_brainpoolP384r1_sha384_p1363_test.json`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::ec::BrainpoolP384r1;

public_keys!(
    brainpoolp384r1,
    BrainpoolP384r1,
    48,
    "ecdsa_brainpoolP384r1_sha384_p1363_test.json"
);
