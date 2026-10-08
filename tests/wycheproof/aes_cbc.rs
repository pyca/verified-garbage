//! AES-CBC with PKCS #5 padding (`IndCpaTest` vectors,
//! `aes_cbc_pkcs5_test.json`).
//!
//! The crate's AES-CBC takes whole blocks and adds no padding, so the
//! padding is added and checked here. A valid vector's ciphertext must be
//! the encryption of its message with its padding, and must decrypt to
//! them. An invalid one is a ciphertext whose decryption, which must still
//! succeed when it is of whole blocks, does not end in valid padding.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use serde::Deserialize;
use verified_garbage::aes_cbc::AesCbc;

use super::harness::{self, Count, Expectation, Hex};
use crate::require_vectors;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Group {
    key_size: usize,
    iv_size: usize,
}

#[derive(Deserialize)]
struct Case {
    key: Hex,
    iv: Hex,
    msg: Hex,
    ct: Hex,
}

/// `msg` with PKCS #5 padding.
fn pad(msg: &[u8]) -> Vec<u8> {
    let n = 16 - msg.len() % 16;
    let mut padded = msg.to_vec();
    padded.resize(msg.len() + n, n as u8);
    padded
}

/// `padded` without its PKCS #5 padding, if that is valid.
fn unpad(padded: &[u8]) -> Option<&[u8]> {
    let n = *padded.last()? as usize;
    let (msg, padding) = padded.split_at_checked(padded.len().checked_sub(n)?)?;
    (1..=16).contains(&n).then_some(())?;
    padding.iter().all(|&b| b as usize == n).then_some(msg)
}

#[test]
fn aes_cbc_pkcs5() {
    require_vectors!();
    let file = harness::load::<Group, Case>("aes_cbc_pkcs5_test.json");
    let (valid, bad_padding) = (Count::default(), Count::default());
    file.par_tests(|group, test| {
        let Case { key, iv, msg, ct } = &test.case;
        let id = test.tc_id;
        assert_eq!(key.0.len() * 8, group.params.key_size, "tcId {id}");
        assert_eq!(group.params.iv_size, 128, "tcId {id}");
        assert_eq!(ct.0.len() % 16, 0, "tcId {id}");
        let ctx = AesCbc::new(&key.0).unwrap();
        let iv: [u8; 16] = iv.0[..].try_into().unwrap();
        let mut chain = iv;
        let mut decrypted = ct.0.clone();
        ctx.decrypt(&mut chain, &mut decrypted).unwrap();
        if test.result == Expectation::Valid {
            assert_eq!(unpad(&decrypted), Some(&msg.0[..]), "tcId {id}");
            let mut encrypted = pad(&msg.0);
            let mut chain = iv;
            ctx.encrypt(&mut chain, &mut encrypted).unwrap();
            assert_eq!(encrypted, ct.0, "tcId {id}");
            valid.add();
        } else {
            assert_eq!(test.result, Expectation::Invalid, "tcId {id}");
            assert_eq!(unpad(&decrypted), None, "tcId {id}");
            bad_padding.add();
        }
    });
    assert_eq!((valid.get(), bad_padding.get()), (72, 144));
}
