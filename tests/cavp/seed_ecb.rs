//! Published SEED vectors; unmodified sources and provenance live under
//! vectors/: RFC 4269's (ECB, with their round keys and intermediate values
//! checked in `lean/VerifiedGarbageTest/Seed.lean`) and pyca/cryptography's
//! CBC, OFB and CFB ones, whose modes are computed here from ECB.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]

use std::collections::BTreeMap;

use verified_garbage::seed_ecb::{Error, SeedEcb};

use super::unhex;

fn key16(key: &[u8]) -> [u8; 16] {
    key.try_into().unwrap()
}

fn encrypt_block(ctx: &SeedEcb, block: &[u8]) -> Vec<u8> {
    let mut out = block.to_vec();
    ctx.encrypt(&mut out).unwrap();
    out
}

fn xor(a: &[u8], b: &[u8]) -> Vec<u8> {
    a.iter().zip(b).map(|(x, y)| x ^ y).collect()
}

/// ECB in both directions, whole and split at every block boundary.
fn check_ecb(key: &[u8], plaintext: &[u8], ciphertext: &[u8]) {
    assert_eq!(plaintext.len(), ciphertext.len());
    let ctx = SeedEcb::new(&key16(key));
    for (operation, input, expected) in [
        (
            SeedEcb::encrypt as fn(&SeedEcb, &mut [u8]) -> Result<(), Error>,
            plaintext,
            ciphertext,
        ),
        (
            SeedEcb::decrypt as fn(&SeedEcb, &mut [u8]) -> Result<(), Error>,
            ciphertext,
            plaintext,
        ),
    ] {
        let mut output = input.to_vec();
        operation(&ctx, &mut output).unwrap();
        assert_eq!(output, expected);
        for offset in (0..=input.len()).step_by(16) {
            let mut output = input.to_vec();
            operation(&ctx, &mut []).unwrap();
            operation(&ctx, &mut output[..offset]).unwrap();
            operation(&ctx, &mut output[offset..]).unwrap();
            assert_eq!(output, expected);
        }
    }
}

#[test]
fn rfc4269() {
    let text = include_str!("../../vectors/rfc4269/rfc4269.txt");
    let appendix = text.split("Appendix B.  Test Vectors").nth(1).unwrap();
    let hexline = |line: &str| unhex(&line.split(':').nth(1).unwrap().replace(' ', ""));
    let mut count = 0;
    let mut lines = appendix.lines().map(str::trim);
    while let Some(line) = lines.next() {
        if !line.starts_with("Key ") {
            continue;
        }
        let key = hexline(line);
        let plaintext = hexline(lines.next().unwrap());
        let ciphertext = hexline(lines.next().unwrap());
        check_ecb(&key, &plaintext, &ciphertext);
        count += 1;
    }
    assert_eq!(count, 4);
}

fn records(text: &str) -> Vec<BTreeMap<&str, &str>> {
    text.split("\n\n")
        .map(|record| {
            record
                .lines()
                .filter_map(|line| line.trim().split_once(" = "))
                .collect::<BTreeMap<_, _>>()
        })
        .filter(|fields| fields.contains_key("COUNT"))
        .collect()
}

#[test]
fn cryptography_cbc() {
    let mut count = 0;
    for f in records(include_str!(
        "../../vectors/cryptography-seed-cbc/rfc-4196.txt"
    )) {
        let ctx = SeedEcb::new(&key16(&unhex(f["KEY"])));
        let plaintext = unhex(f["PLAINTEXT"]);
        let ciphertext = unhex(f["CIPHERTEXT"]);
        let mut chain = unhex(f["IV"]);
        let mut decrypted = ciphertext.clone();
        ctx.decrypt(&mut decrypted).unwrap();
        for ((p, c), d) in plaintext
            .chunks(16)
            .zip(ciphertext.chunks(16))
            .zip(decrypted.chunks(16))
        {
            assert_eq!(encrypt_block(&ctx, &xor(p, &chain)), c);
            assert_eq!(xor(d, &chain), p);
            chain = c.to_vec();
        }
        count += 1;
    }
    assert!(count >= 2);
}

#[test]
fn cryptography_ofb() {
    let mut count = 0;
    for f in records(include_str!(
        "../../vectors/cryptography-seed-ofb/seed-ofb.txt"
    )) {
        let ctx = SeedEcb::new(&key16(&unhex(f["KEY"])));
        let mut stream = unhex(f["IV"]);
        let plaintext = unhex(f["PLAINTEXT"]);
        let ciphertext = unhex(f["CIPHERTEXT"]);
        for (p, c) in plaintext.chunks(16).zip(ciphertext.chunks(16)) {
            stream = encrypt_block(&ctx, &stream);
            assert_eq!(xor(p, &stream), c);
        }
        count += 1;
    }
    assert!(count >= 2);
}

#[test]
fn cryptography_cfb() {
    let mut count = 0;
    for f in records(include_str!(
        "../../vectors/cryptography-seed-cfb/seed-cfb.txt"
    )) {
        let ctx = SeedEcb::new(&key16(&unhex(f["KEY"])));
        let mut chain = unhex(f["IV"]);
        let plaintext = unhex(f["PLAINTEXT"]);
        let ciphertext = unhex(f["CIPHERTEXT"]);
        for (p, c) in plaintext.chunks(16).zip(ciphertext.chunks(16)) {
            assert_eq!(xor(p, &encrypt_block(&ctx, &chain)), c);
            chain = c.to_vec();
        }
        count += 1;
    }
    assert!(count >= 2);
}

/// Many blocks at once, across batches of sixteen, agree with one at a time.
#[test]
fn batches() {
    // Generated inputs test agreement between batch sizes, not known answers.
    let ctx = SeedEcb::new(&[7; 16]);
    let input: Vec<u8> = (0..16 * 50).map(|i| i as u8).collect();
    for blocks in [1, 15, 16, 17, 31, 32, 33, 50] {
        let input = &input[..16 * blocks];
        let mut whole = input.to_vec();
        ctx.encrypt(&mut whole).unwrap();
        let single: Vec<u8> = input
            .chunks(16)
            .flat_map(|b| encrypt_block(&ctx, b))
            .collect();
        assert_eq!(whole, single);
        ctx.decrypt(&mut whole).unwrap();
        assert_eq!(whole, input);
    }
}

#[test]
fn incomplete() {
    let ctx = SeedEcb::new(&[0; 16]);
    for length in [1, 15, 17, 31] {
        let mut buffer = vec![0x5a; length];
        assert_eq!(ctx.encrypt(&mut buffer), Err(Error::IncompleteBlock));
        assert_eq!(ctx.decrypt(&mut buffer), Err(Error::IncompleteBlock));
        assert!(buffer.iter().all(|&b| b == 0x5a));
    }
}
