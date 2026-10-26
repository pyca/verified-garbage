//! PBKDF2 (`PbkdfTest` vectors): the checks every hash function's tests
//! (`pbkdf2_<hash>.rs`) run.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use core::num::NonZeroU32;

use super::harness::{self, Expectation, Fields, Hex};

crate::json_struct! {
    struct Case {
        password: Hex = "password",
        salt: Hex = "salt",
        iteration_count: u32 = "iterationCount",
        dk_len: usize = "dkLen",
        dk: Hex = "dk",
    }
}

/// Every vector of `name` must derive exactly its key (the files only have
/// valid vectors), with `derive`.
pub(crate) fn check_with(name: &str, derive: fn(&[u8], &[u8], NonZeroU32, &mut [u8])) {
    let file = harness::load::<Fields, Case>(name);
    file.par_tests(|_, test| {
        let c = &test.case;
        assert_eq!(test.result, Expectation::Valid, "tcId {}", test.tc_id);
        let mut dk = vec![0u8; c.dk_len];
        derive(
            &c.password.0,
            &c.salt.0,
            NonZeroU32::new(c.iteration_count).unwrap(),
            &mut dk,
        );
        assert_eq!(dk, c.dk.0, "tcId {}", test.tc_id);
    });
}
