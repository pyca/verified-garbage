//! Triple DES-CFB8: NIST CAVP's multi-block message tests, unmodified under
//! vectors/; and CFB8 from ECB (`TripleDesEcb`, tested on CAVP's ECB
//! vectors) on every length up to a few dozen bytes, for each key length.

#![cfg(target_arch = "x86_64")]

use std::collections::BTreeMap;

use verified_garbage::triple_des_cfb8::{InvalidKeyLength, TripleDesCfb8};
use verified_garbage::triple_des_ecb::TripleDesEcb;

use super::unhex;

/// CFB8 from ECB: the output and the input block to continue from.
fn reference(key: &[u8], iv: [u8; 8], data: &[u8], encrypt: bool) -> (Vec<u8>, [u8; 8]) {
    let ecb = TripleDesEcb::new(key).unwrap();
    let mut input = iv;
    let mut out = Vec::new();
    for &x in data {
        let mut o = input;
        ecb.encrypt(&mut o).unwrap();
        let y = x ^ o[0];
        input.rotate_left(1);
        input[7] = if encrypt { y } else { x };
        out.push(y);
    }
    (out, input)
}

/// The input block after `ciphertext` from `iv`.
fn after(iv: [u8; 8], ciphertext: &[u8]) -> [u8; 8] {
    let mut all = iv.to_vec();
    all.extend_from_slice(ciphertext);
    all[all.len() - 8..].try_into().unwrap()
}

/// `plaintext` encrypts to `ciphertext` and decrypts back, whole and split
/// at every byte.
fn check(ctx: &TripleDesCfb8, iv: [u8; 8], plaintext: &[u8], ciphertext: &[u8]) {
    let next = after(iv, ciphertext);
    for offset in 0..=plaintext.len() {
        let mut chain = iv;
        let mut buffer = plaintext.to_vec();
        ctx.encrypt(&mut chain, &mut buffer[..offset]);
        ctx.encrypt(&mut chain, &mut buffer[offset..]);
        assert_eq!(buffer, ciphertext);
        assert_eq!(chain, next);
        let mut chain = iv;
        ctx.decrypt(&mut chain, &mut buffer[..offset]);
        ctx.decrypt(&mut chain, &mut buffer[offset..]);
        assert_eq!(buffer, plaintext);
        assert_eq!(chain, next);
    }
}

fn check_file(text: &str) -> usize {
    let mut count = 0;
    for record in text.replace('\r', "").split("\n\n") {
        let fields: BTreeMap<_, _> = record
            .lines()
            .filter_map(|line| line.trim().split_once(" = "))
            .collect();
        if !fields.contains_key("COUNT") {
            continue;
        }
        let mut key = unhex(fields["KEY1"]);
        key.extend(unhex(fields["KEY2"]));
        key.extend(unhex(fields["KEY3"]));
        let iv: [u8; 8] = unhex(fields["IV"]).try_into().unwrap();
        let plaintext = unhex(fields["PLAINTEXT"]);
        let ciphertext = unhex(fields["CIPHERTEXT"]);
        check(
            &TripleDesCfb8::new(&key).unwrap(),
            iv,
            &plaintext,
            &ciphertext,
        );
        if key[..8] == key[16..] {
            check(
                &TripleDesCfb8::new(&key[..16]).unwrap(),
                iv,
                &plaintext,
                &ciphertext,
            );
        }
        count += 1;
    }
    count
}

#[test]
fn cavp_mmt() {
    assert_eq!(
        check_file(include_str!(
            "../../vectors/nist-cavp-tdes-mmt/TCFB8MMT2.rsp"
        )),
        10
    );
    assert_eq!(
        check_file(include_str!(
            "../../vectors/nist-cavp-tdes-mmt/TCFB8MMT3.rsp"
        )),
        20
    );
}

/// Every length up to 40 bytes, in each direction.
#[test]
fn from_ecb() {
    let data: Vec<u8> = (0..40).map(|i| (i * 31 + 7) as u8).collect();
    let iv: [u8; 8] = core::array::from_fn(|i| (i * 11 + 5) as u8);
    for key_len in [16, 24] {
        let key: Vec<u8> = (0..key_len).map(|i| (17 * i + 3) as u8).collect();
        let ctx = TripleDesCfb8::new(&key).unwrap();
        for len in 0..=data.len() {
            for encrypt in [true, false] {
                let (output, next) = reference(&key, iv, &data[..len], encrypt);
                let mut chain = iv;
                let mut buffer = data[..len].to_vec();
                if encrypt {
                    ctx.encrypt(&mut chain, &mut buffer);
                } else {
                    ctx.decrypt(&mut chain, &mut buffer);
                }
                assert_eq!(buffer, output);
                assert_eq!(chain, next);
            }
        }
    }
}

#[test]
fn errors() {
    for len in [0, 8, 15, 17, 32] {
        assert_eq!(
            TripleDesCfb8::new(&vec![0; len]).err(),
            Some(InvalidKeyLength)
        );
    }
}
