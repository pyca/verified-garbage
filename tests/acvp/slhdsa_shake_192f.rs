//! SLH-DSA-SHAKE-192f (FIPS 205): the tests of `slhdsa.rs`.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

super::slhdsa::slhdsa_tests!("SLH-DSA-SHAKE-192f", slhdsa_shake_192f, 24, true);
