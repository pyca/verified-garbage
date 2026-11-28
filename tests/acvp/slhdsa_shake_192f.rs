//! SLH-DSA-SHAKE-192f (FIPS 205): the tests of `slhdsa.rs`.

#![cfg(target_arch = "x86_64")]

super::slhdsa::slhdsa_tests!("SLH-DSA-SHAKE-192f", slhdsa_shake_192f, 24);
