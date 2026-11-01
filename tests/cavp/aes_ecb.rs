//! NIST CAVP AES-ECB known-answer (KAT) and multi-block message (MMT)
//! vectors, with unmodified sources under vectors/.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use std::collections::BTreeMap;

use verified_garbage::aes_ecb::{AesEcb, Error};

use super::unhex;

type Operation = fn(&AesEcb, &mut [u8]) -> Result<(), Error>;

/// Checks a vector in both directions, in one call; with `split`, also in
/// two calls split at each block boundary and one call per block.
fn check(key: &[u8], plaintext: &[u8], ciphertext: &[u8], split: bool) {
    assert_eq!(plaintext.len(), ciphertext.len());
    let ctx = AesEcb::new(key).unwrap();
    for (operation, input, expected) in [
        (AesEcb::encrypt as Operation, plaintext, ciphertext),
        (AesEcb::decrypt as Operation, ciphertext, plaintext),
    ] {
        let mut output = input.to_vec();
        operation(&ctx, &mut output).unwrap();
        assert_eq!(output, expected);
        if split {
            for offset in (0..=input.len()).step_by(16) {
                let mut output = input.to_vec();
                operation(&ctx, &mut []).unwrap();
                operation(&ctx, &mut output[..offset]).unwrap();
                operation(&ctx, &mut output[offset..]).unwrap();
                assert_eq!(output, expected);
            }
            let mut output = input.to_vec();
            for block in output.chunks_mut(16) {
                operation(&ctx, block).unwrap();
            }
            assert_eq!(output, expected);
        }
    }
}

/// Checks every vector of a response file, and returns how many there were.
fn check_file(text: &str, split: bool) -> usize {
    let mut count = 0;
    for record in text.replace('\r', "").split("\n\n") {
        let fields: BTreeMap<_, _> = record
            .lines()
            .filter_map(|line| line.trim().split_once(" = "))
            .collect();
        if !fields.contains_key("COUNT") {
            continue;
        }
        check(
            &unhex(fields["KEY"]),
            &unhex(fields["PLAINTEXT"]),
            &unhex(fields["CIPHERTEXT"]),
            split,
        );
        count += 1;
    }
    count
}

#[test]
fn nist_ecb() {
    let files = [
        (
            crate::vectors::text("vectors/nist-cavp/aes/ECBGFSbox128.rsp"),
            14,
            false,
        ),
        (
            crate::vectors::text("vectors/nist-cavp/aes/ECBGFSbox192.rsp"),
            12,
            false,
        ),
        (
            crate::vectors::text("vectors/nist-cavp/aes/ECBGFSbox256.rsp"),
            10,
            false,
        ),
        (
            crate::vectors::text("vectors/nist-cavp/aes/ECBKeySbox128.rsp"),
            42,
            false,
        ),
        (
            crate::vectors::text("vectors/nist-cavp/aes/ECBKeySbox192.rsp"),
            48,
            false,
        ),
        (
            crate::vectors::text("vectors/nist-cavp/aes/ECBKeySbox256.rsp"),
            32,
            false,
        ),
        (
            crate::vectors::text("vectors/nist-cavp/aes/ECBVarKey128.rsp"),
            256,
            false,
        ),
        (
            crate::vectors::text("vectors/nist-cavp/aes/ECBVarKey192.rsp"),
            384,
            false,
        ),
        (
            crate::vectors::text("vectors/nist-cavp/aes/ECBVarKey256.rsp"),
            512,
            false,
        ),
        (
            crate::vectors::text("vectors/nist-cavp/aes/ECBVarTxt128.rsp"),
            256,
            false,
        ),
        (
            crate::vectors::text("vectors/nist-cavp/aes/ECBVarTxt192.rsp"),
            256,
            false,
        ),
        (
            crate::vectors::text("vectors/nist-cavp/aes/ECBVarTxt256.rsp"),
            256,
            false,
        ),
        (
            crate::vectors::text("vectors/nist-cavp-aes-mmt/ECBMMT128.rsp"),
            20,
            true,
        ),
        (
            crate::vectors::text("vectors/nist-cavp-aes-mmt/ECBMMT192.rsp"),
            20,
            true,
        ),
        (
            crate::vectors::text("vectors/nist-cavp-aes-mmt/ECBMMT256.rsp"),
            20,
            true,
        ),
    ];
    let mut total = 0;
    for (text, expected, split) in files {
        let count = check_file(text, split);
        assert_eq!(count, expected);
        total += count;
    }
    assert_eq!(total, 2138);
}

/// The known-answer files' vectors with the same key and direction, in
/// runs, each transformed in one call: for every length up to 41 blocks (two
/// of the VAES code's groups of sixteen, one of eight and one more), and the
/// whole run (up to the 128 vectors of `ECBVarTxt`'s).
#[test]
fn nist_ecb_runs() {
    let files = [
        crate::vectors::text("vectors/nist-cavp/aes/ECBGFSbox128.rsp"),
        crate::vectors::text("vectors/nist-cavp/aes/ECBGFSbox192.rsp"),
        crate::vectors::text("vectors/nist-cavp/aes/ECBGFSbox256.rsp"),
        crate::vectors::text("vectors/nist-cavp/aes/ECBKeySbox128.rsp"),
        crate::vectors::text("vectors/nist-cavp/aes/ECBKeySbox192.rsp"),
        crate::vectors::text("vectors/nist-cavp/aes/ECBKeySbox256.rsp"),
        crate::vectors::text("vectors/nist-cavp/aes/ECBVarKey128.rsp"),
        crate::vectors::text("vectors/nist-cavp/aes/ECBVarKey192.rsp"),
        crate::vectors::text("vectors/nist-cavp/aes/ECBVarKey256.rsp"),
        crate::vectors::text("vectors/nist-cavp/aes/ECBVarTxt128.rsp"),
        crate::vectors::text("vectors/nist-cavp/aes/ECBVarTxt192.rsp"),
        crate::vectors::text("vectors/nist-cavp/aes/ECBVarTxt256.rsp"),
    ];
    struct Run {
        key: Vec<u8>,
        encrypt: bool,
        input: Vec<u8>,
        output: Vec<u8>,
    }
    let mut runs: Vec<Run> = Vec::new();
    for text in files {
        let mut encrypt = true;
        for record in text.replace('\r', "").split("\n\n") {
            match record.trim() {
                "[ENCRYPT]" => encrypt = true,
                "[DECRYPT]" => encrypt = false,
                _ => {}
            }
            let fields: BTreeMap<_, _> = record
                .lines()
                .filter_map(|line| line.trim().split_once(" = "))
                .collect();
            if !fields.contains_key("COUNT") {
                continue;
            }
            let key = unhex(fields["KEY"]);
            let (plaintext, ciphertext) = (unhex(fields["PLAINTEXT"]), unhex(fields["CIPHERTEXT"]));
            let (input, output) = if encrypt {
                (plaintext, ciphertext)
            } else {
                (ciphertext, plaintext)
            };
            match runs.last_mut() {
                Some(run) if run.key == key && run.encrypt == encrypt => {
                    run.input.extend(input);
                    run.output.extend(output);
                }
                _ => runs.push(Run {
                    key,
                    encrypt,
                    input,
                    output,
                }),
            }
        }
    }
    let mut vectors = 0;
    for Run {
        key,
        encrypt,
        input,
        output,
    } in &runs
    {
        let ctx = AesEcb::new(key).unwrap();
        let operation = if *encrypt {
            AesEcb::encrypt as Operation
        } else {
            AesEcb::decrypt as Operation
        };
        let n = input.len() / 16;
        for m in (0..=n.min(41)).chain([n]) {
            let mut data = input.clone();
            operation(&ctx, &mut data[..16 * m]).unwrap();
            assert_eq!(data[..16 * m], output[..16 * m]);
            assert_eq!(data[16 * m..], input[16 * m..]);
        }
        vectors += n;
    }
    // Every vector of the twelve files.
    assert_eq!(vectors, 2078);
    assert_eq!(runs.iter().map(|run| run.input.len() / 16).max(), Some(128));
    assert!(runs.iter().any(|run| !run.encrypt));
}

#[test]
fn limits_and_empty_input() {
    for len in 0..=40 {
        let key: Vec<_> = (0..len).map(|i| (17 * i + 3) as u8).collect();
        if !matches!(len, 16 | 24 | 32) {
            assert!(matches!(AesEcb::new(&key), Err(Error::InvalidKeyLength)));
            continue;
        }
        let ctx = AesEcb::new(&key).unwrap();
        ctx.encrypt(&mut []).unwrap();
        ctx.decrypt(&mut []).unwrap();
        for n in 1usize..48 {
            if n.is_multiple_of(16) {
                continue;
            }
            let mut buffer = vec![0x5a; n];
            assert_eq!(ctx.encrypt(&mut buffer), Err(Error::IncompleteBlock));
            assert_eq!(buffer, vec![0x5a; n]);
            assert_eq!(ctx.decrypt(&mut buffer), Err(Error::IncompleteBlock));
            assert_eq!(buffer, vec![0x5a; n]);
        }
        // Many blocks in one call round-trip, and equal blocks encrypt to
        // equal blocks.
        let mut buffer = vec![0xa5; 16 * 67];
        ctx.encrypt(&mut buffer).unwrap();
        assert!(buffer.chunks(16).all(|b| b == &buffer[..16]));
        assert_ne!(&buffer[..16], &[0xa5; 16]);
        ctx.decrypt(&mut buffer).unwrap();
        assert_eq!(buffer, vec![0xa5; 16 * 67]);
    }
}
