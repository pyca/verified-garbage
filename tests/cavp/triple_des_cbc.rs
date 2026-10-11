//! Triple DES-CBC: NIST CAVP's multi-block message tests, unmodified under
//! vectors/; and CBC from ECB (`TripleDesEcb`, tested on CAVP's ECB
//! vectors) on every length up to a few dozen blocks, for each key length.

#![cfg(target_arch = "x86_64")]

use std::collections::BTreeMap;

use verified_garbage::triple_des_cbc::{Error, TripleDesCbc};
use verified_garbage::triple_des_ecb::TripleDesEcb;

use super::unhex;

/// CBC encryption from ECB, one block at a time.
fn reference(key: &[u8], iv: [u8; 8], data: &[u8]) -> Vec<u8> {
    let ecb = TripleDesEcb::new(key).unwrap();
    let mut chain = iv;
    let mut out = Vec::new();
    for block in data.chunks(8) {
        let mut b: Vec<u8> = block.iter().zip(&chain).map(|(x, y)| x ^ y).collect();
        ecb.encrypt(&mut b).unwrap();
        chain.copy_from_slice(&b);
        out.extend_from_slice(&b);
    }
    out
}

/// `plaintext` encrypts to `ciphertext` and decrypts back, whole and split
/// at every block boundary, leaving the last ciphertext block as the
/// chaining value.
fn check(ctx: &TripleDesCbc, iv: [u8; 8], plaintext: &[u8], ciphertext: &[u8]) {
    let after: [u8; 8] = match ciphertext.len() {
        0 => iv,
        len => ciphertext[len - 8..].try_into().unwrap(),
    };
    for offset in (0..=plaintext.len()).step_by(8) {
        let mut chain = iv;
        let mut buffer = plaintext.to_vec();
        ctx.encrypt(&mut chain, &mut buffer[..offset]).unwrap();
        ctx.encrypt(&mut chain, &mut buffer[offset..]).unwrap();
        assert_eq!(buffer, ciphertext);
        assert_eq!(chain, after);
        let mut chain = iv;
        ctx.decrypt(&mut chain, &mut buffer[..offset]).unwrap();
        ctx.decrypt(&mut chain, &mut buffer[offset..]).unwrap();
        assert_eq!(buffer, plaintext);
        assert_eq!(chain, after);
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
            &TripleDesCbc::new(&key).unwrap(),
            iv,
            &plaintext,
            &ciphertext,
        );
        if key[..8] == key[16..] {
            check(
                &TripleDesCbc::new(&key[..16]).unwrap(),
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
            "../../vectors/nist-cavp-tdes-mmt/TCBCMMT2.rsp"
        )),
        10
    );
    assert_eq!(
        check_file(include_str!(
            "../../vectors/nist-cavp-tdes-mmt/TCBCMMT3.rsp"
        )),
        20
    );
}

/// Every number of blocks up to 27.
#[test]
fn from_ecb() {
    let data: Vec<u8> = (0..8 * 27).map(|i| (i * 31 + 7) as u8).collect();
    let iv: [u8; 8] = core::array::from_fn(|i| (i * 11 + 5) as u8);
    for key_len in [16, 24] {
        let key: Vec<u8> = (0..key_len).map(|i| (17 * i + 3) as u8).collect();
        let ctx = TripleDesCbc::new(&key).unwrap();
        for blocks in 0..=27 {
            let input = &data[..8 * blocks];
            check(&ctx, iv, input, &reference(&key, iv, input));
        }
    }
}

#[test]
fn errors() {
    for len in [0, 8, 15, 17, 32] {
        assert!(matches!(
            TripleDesCbc::new(&vec![0; len]),
            Err(Error::InvalidKeyLength)
        ));
    }
    let ctx = TripleDesCbc::new(&[0; 24]).unwrap();
    for len in [1, 7, 9, 15] {
        let mut chain = [7; 8];
        let mut buffer = vec![0x5a; len];
        assert_eq!(
            ctx.encrypt(&mut chain, &mut buffer),
            Err(Error::IncompleteBlock)
        );
        assert_eq!(
            ctx.decrypt(&mut chain, &mut buffer),
            Err(Error::IncompleteBlock)
        );
        assert_eq!(buffer, vec![0x5a; len]);
        assert_eq!(chain, [7; 8]);
    }
}
