//! SEC 1 conversions over P-384: the public keys of `ecdsa_secp384r1_sha384_p1363_test.json`,
//! and the compressed peers of `ecdh_secp384r1_ecpoint_test.json`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::ecdh::P384;

public_keys!(p384, P384, 48, "ecdsa_secp384r1_sha384_p1363_test.json");
compressed_peers!(p384_peers, P384, 48, "ecdh_secp384r1_ecpoint_test.json");
