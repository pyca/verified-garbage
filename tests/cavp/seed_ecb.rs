//! SEED-ECB: RFC 4269's vectors, unmodified under vectors/ (with their round
//! keys and intermediate values checked in
//! `lean/VerifiedGarbageTest/Seed.lean`). The modes' vectors are in
//! `seed_cbc.rs`, `seed_cfb.rs` and `seed_ofb.rs`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::seed_ecb::{Error, SeedEcb};

use verified_garbage_test_vectors::unhex;

fn key16(key: &[u8]) -> [u8; 16] {
    key.try_into().unwrap()
}

fn encrypt_block(ctx: &SeedEcb, block: &[u8]) -> Vec<u8> {
    let mut out = block.to_vec();
    ctx.encrypt(&mut out).unwrap();
    out
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
    let text = crate::vectors::text("vectors/rfc4269/rfc4269.txt");
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

/// Many blocks at once, at lengths around multiples of sixteen blocks, agree
/// with one at a time.
#[test]
fn batches() {
    // Generated inputs test agreement between lengths, not known answers.
    let ctx = SeedEcb::new(&[7; 16]);
    let input: Vec<u8> = crate::bytes::pattern(16 * 50, 1, 0);
    for blocks in [1, 15, 16, 17, 31, 32, 33, 50] {
        let input = &input[..16 * blocks];
        let mut whole = input.to_vec();
        ctx.encrypt(&mut whole).unwrap();
        let mut single = Vec::new();
        for block in input.chunks(16) {
            single.extend(encrypt_block(&ctx, block));
        }
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
        assert!(crate::bytes::all_equal(&buffer, 0x5a));
    }
}
