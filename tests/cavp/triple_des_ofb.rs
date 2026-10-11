//! Triple DES-OFB: NIST CAVP's multi-block message tests, unmodified under
//! vectors/; and OFB from ECB (`TripleDesEcb`, tested on CAVP's ECB vectors)
//! on every length up to a few dozen blocks, partial last blocks included,
//! for each key length.

#![cfg(target_arch = "x86_64")]

use std::collections::BTreeMap;

use verified_garbage::triple_des_ecb::TripleDesEcb;
use verified_garbage::triple_des_ofb::{InvalidKeyLength, TripleDesOfb};

use super::unhex;

/// OFB from ECB: the output and the last output block used.
fn reference(key: &[u8], iv: [u8; 8], data: &[u8]) -> (Vec<u8>, [u8; 8]) {
    let ecb = TripleDesEcb::new(key).unwrap();
    let mut o = iv;
    let mut out = Vec::new();
    for block in data.chunks(8) {
        ecb.encrypt(&mut o).unwrap();
        out.extend(block.iter().zip(&o).map(|(x, y)| x ^ y));
    }
    (out, o)
}

/// `input` transforms to `output`, whole and split at every block boundary,
/// leaving `after` as the block to continue from.
fn check(ctx: &TripleDesOfb, iv: [u8; 8], input: &[u8], output: &[u8], after: [u8; 8]) {
    for offset in (0..=input.len()).step_by(8) {
        let mut chain = iv;
        let mut buffer = input.to_vec();
        ctx.apply_keystream(&mut chain, &mut buffer[..offset]);
        ctx.apply_keystream(&mut chain, &mut buffer[offset..]);
        assert_eq!(buffer, output);
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
        // The last output block: the last blocks' XOR.
        let n = plaintext.len();
        let after: [u8; 8] = core::array::from_fn(|i| plaintext[n - 8 + i] ^ ciphertext[n - 8 + i]);
        let mut keys = vec![key.clone()];
        if key[..8] == key[16..] {
            keys.push(key[..16].to_vec());
        }
        for key in keys {
            let ctx = TripleDesOfb::new(&key).unwrap();
            check(&ctx, iv, &plaintext, &ciphertext, after);
            check(&ctx, iv, &ciphertext, &plaintext, after);
        }
        count += 1;
    }
    count
}

#[test]
fn cavp_mmt() {
    assert_eq!(
        check_file(include_str!(
            "../../vectors/nist-cavp-tdes-mmt/TOFBMMT2.rsp"
        )),
        10
    );
    assert_eq!(
        check_file(include_str!(
            "../../vectors/nist-cavp-tdes-mmt/TOFBMMT3.rsp"
        )),
        20
    );
}

/// Every length up to 27 blocks.
#[test]
fn from_ecb() {
    let data: Vec<u8> = (0..8 * 27).map(|i| (i * 31 + 7) as u8).collect();
    let iv: [u8; 8] = core::array::from_fn(|i| (i * 11 + 5) as u8);
    for key_len in [16, 24] {
        let key: Vec<u8> = (0..key_len).map(|i| (17 * i + 3) as u8).collect();
        let ctx = TripleDesOfb::new(&key).unwrap();
        for len in 0..=data.len() {
            let (output, after) = reference(&key, iv, &data[..len]);
            let mut chain = iv;
            let mut buffer = data[..len].to_vec();
            ctx.apply_keystream(&mut chain, &mut buffer);
            assert_eq!(buffer, output);
            assert_eq!(chain, after);
        }
    }
}

#[test]
fn errors() {
    for len in [0, 8, 15, 17, 32] {
        assert_eq!(
            TripleDesOfb::new(&vec![0; len]).err(),
            Some(InvalidKeyLength)
        );
    }
}
