//! SEC 1 conversions over brainpoolP320r1: the public keys of `ecdsa_brainpoolP320r1_sha384_p1363_test.json`.

#![cfg(target_arch = "x86_64")]

use verified_garbage::ec::BrainpoolP320r1;

public_keys!(
    brainpoolp320r1,
    BrainpoolP320r1,
    40,
    "ecdsa_brainpoolP320r1_sha384_p1363_test.json"
);
