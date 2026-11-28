//! SLH-DSA-SHAKE-256s (FIPS 205): the tests of `slhdsa.rs`.

#![cfg(target_arch = "x86_64")]

super::slhdsa::slhdsa_tests!("SLH-DSA-SHAKE-256s", slhdsa_shake_256s, 32);
