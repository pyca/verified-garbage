//! SLH-DSA-SHAKE-128s (FIPS 205): the tests of `slhdsa.rs`.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

super::slhdsa::slhdsa_tests!("SLH-DSA-SHAKE-128s", slhdsa_shake_128s, 16, false);
