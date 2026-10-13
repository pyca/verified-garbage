//! The 900 NESSIE IDEA vectors, from pyca/cryptography's
//! `idea-ecb.txt`, unmodified under `vectors/cryptography-idea/`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

use std::collections::BTreeMap;

use verified_garbage::idea_ecb::{Error, IdeaEcb};

const TEXT: &str = include_str!("../../vectors/cryptography-idea/idea-ecb.txt");

fn unhex(s: &str) -> Vec<u8> {
    assert_eq!(s.len() % 2, 0);
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

/// Encrypts or decrypts `input` with `operation`, whole, in two pieces at
/// every block boundary (with empty calls around them), and a block at a
/// time, and checks each against `expected`.
fn check(
    ctx: &IdeaEcb,
    operation: fn(&IdeaEcb, &mut [u8]) -> Result<(), Error>,
    input: &[u8],
    expected: &[u8],
) {
    let mut output = input.to_vec();
    operation(ctx, &mut output).unwrap();
    assert_eq!(output, expected);
    for offset in (0..=input.len()).step_by(8) {
        let mut output = input.to_vec();
        operation(ctx, &mut []).unwrap();
        operation(ctx, &mut output[..offset]).unwrap();
        operation(ctx, &mut output[offset..]).unwrap();
        assert_eq!(output, expected);
    }
    let mut output = input.to_vec();
    for block in output.chunks_mut(8) {
        operation(ctx, block).unwrap();
    }
    assert_eq!(output, expected);
}

#[test]
fn nessie() {
    // The vectors of each key, in order, for multi-block ECB.
    let mut by_key: BTreeMap<Vec<u8>, (Vec<u8>, Vec<u8>)> = BTreeMap::new();
    let mut count = 0;
    let mut iterated = 0;
    for record in TEXT.replace('\r', "").split("\n\n") {
        let fields: BTreeMap<_, _> = record
            .lines()
            .filter_map(|line| line.trim().split_once(" = "))
            .collect();
        let Some(key) = fields.get("KEY") else {
            continue;
        };
        let key = unhex(key);
        let pt = unhex(fields["PLAINTEXT"]);
        let ct = unhex(fields["CIPHERTEXT"]);
        let ctx = IdeaEcb::new(&key).unwrap();
        let mut block = pt.clone();
        ctx.encrypt(&mut block).unwrap();
        assert_eq!(block, ct);
        ctx.decrypt(&mut block).unwrap();
        assert_eq!(block, pt);
        // NESSIE's "Iterated 100 times" and "Iterated 1000 times".
        for n in [100, 1000] {
            if let Some(out) = fields.get(format!("CIPHERTEXT{n}").as_str()) {
                let out = unhex(out);
                let mut block = pt.clone();
                for _ in 0..n {
                    ctx.encrypt(&mut block).unwrap();
                }
                assert_eq!(block, out);
                for _ in 0..n {
                    ctx.decrypt(&mut block).unwrap();
                }
                assert_eq!(block, pt);
                iterated += 1;
            }
        }
        let entry = by_key.entry(key).or_default();
        entry.0.extend_from_slice(&pt);
        entry.1.extend_from_slice(&ct);
        count += 1;
    }
    assert_eq!(count, 900);
    assert_eq!(iterated, 900);
    for (key, (pt, ct)) in by_key {
        let ctx = IdeaEcb::new(&key).unwrap();
        check(&ctx, IdeaEcb::encrypt, &pt, &ct);
        check(&ctx, IdeaEcb::decrypt, &ct, &pt);
    }
}

#[test]
fn errors() {
    for len in [0, 15, 17, 24, 32] {
        assert!(matches!(
            IdeaEcb::new(&vec![0; len]),
            Err(Error::InvalidKeyLength)
        ));
    }
    let ctx = IdeaEcb::new(&[0; 16]).unwrap();
    for len in [1, 7, 9, 15] {
        let mut buffer = vec![0xa5; len];
        assert_eq!(ctx.encrypt(&mut buffer), Err(Error::IncompleteBlock));
        assert_eq!(ctx.decrypt(&mut buffer), Err(Error::IncompleteBlock));
        assert!(buffer.iter().all(|&b| b == 0xa5));
    }
}
