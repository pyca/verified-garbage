//! XTS-AES (`IndCpaTest` vectors, `aes_xts_test.json`).
//!
//! A vector's tweak value `iv` may be shorter than a block; it is the start
//! of the 16-byte tweak value, the rest zeros (a data unit's number,
//! little-endian). Every vector is valid: its message must encrypt to its
//! ciphertext, which must decrypt back.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::aes_xts::AesXts;

use super::harness::{self, Count, Expectation};
use super::schema::{CipherCase as Case, SizesGroup as Group};
use crate::require_vectors;

#[test]
fn aes_xts() {
    require_vectors!();
    let file = harness::load::<Group, Case>("aes_xts_test.json");
    let valid = Count::default();
    file.par_tests(|group, test| {
        let Case { key, iv, msg, ct } = &test.case;
        let id = test.tc_id;
        assert_eq!(test.result, Expectation::Valid, "tcId {id}");
        assert_eq!(Some(key.0.len() * 8), group.params.key_size, "tcId {id}");
        assert_eq!(Some(iv.0.len() * 8), group.params.iv_size, "tcId {id}");
        let ctx = AesXts::new(&key.0).unwrap();
        let mut i = [0; 16];
        i[..iv.0.len()].copy_from_slice(&iv.0);
        let mut buffer = msg.0.clone();
        ctx.encrypt(&i, &mut buffer).unwrap();
        assert_eq!(buffer, ct.0, "tcId {id}");
        ctx.decrypt(&i, &mut buffer).unwrap();
        assert_eq!(buffer, msg.0, "tcId {id}");
        valid.add();
    });
    assert_eq!(valid.get(), 123);
}
