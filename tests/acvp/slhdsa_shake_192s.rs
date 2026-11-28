//! SLH-DSA-SHAKE-192s (FIPS 205): the tests of `slhdsa.rs`.

#![cfg(target_arch = "x86_64")]

super::slhdsa::slhdsa_tests!("SLH-DSA-SHAKE-192s", slhdsa_shake_192s, 24);
