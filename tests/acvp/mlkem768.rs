//! ML-KEM-768 (FIPS 203): the tests of `mlkem.rs`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
))]

super::mlkem::mlkem_tests!(
    "ML-KEM-768",
    verified_garbage::mlkem768,
    DecapsulationKey768,
    EncapsulationKey768
);
