//! SLH-DSA-SHAKE-192s (FIPS 205): the tests of `slhdsa.rs`.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

super::slhdsa::slhdsa_tests!("SLH-DSA-SHAKE-192s", slhdsa_shake_192s, 24, false);
