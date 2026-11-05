//! NIST CAVP AES-CFB8 known-answer (KAT) and multi-block message (MMT)
//! vectors, with unmodified sources under vectors/.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::cipher::aes::{AesCfb8Decryptor, AesCfb8Encryptor};
use verified_garbage::error::InvalidKeyLength;

use verified_garbage_test_vectors::{cavp_records, unhex};

/// Encrypts (or decrypts) `buffer` with `key` from `iv`, in the pieces
/// `lens` gives (the rest in a last piece).
fn run(key: &[u8], iv: &[u8; 16], encrypt: bool, buffer: &mut [u8], lens: &[usize]) {
    let mut encryptor = AesCfb8Encryptor::new(key, iv).unwrap();
    let mut decryptor = AesCfb8Decryptor::new(key, iv).unwrap();
    let mut rest = buffer;
    for &len in lens.iter().chain([&usize::MAX]) {
        let (piece, tail) = rest.split_at_mut(len.min(rest.len()));
        if encrypt {
            encryptor.encrypt(piece);
        } else {
            decryptor.decrypt(piece);
        }
        rest = tail;
    }
}

/// Checks a vector in both directions, in one call; with `split`, also in
/// two calls split at each length (after an empty one), one call per byte,
/// and with the message cut short at each length.
fn check(key: &[u8], iv: &[u8], plaintext: &[u8], ciphertext: &[u8], split: bool) {
    assert_eq!(plaintext.len(), ciphertext.len());
    let iv: [u8; 16] = iv.try_into().unwrap();
    for (encrypt, input, expected) in [
        (true, plaintext, ciphertext),
        (false, ciphertext, plaintext),
    ] {
        let mut output = input.to_vec();
        run(key, &iv, encrypt, &mut output, &[]);
        assert_eq!(output, expected);
        if split {
            for offset in 0..=input.len() {
                let mut output = input.to_vec();
                run(key, &iv, encrypt, &mut output, &[0, offset]);
                assert_eq!(output, expected);
            }
            let mut output = input.to_vec();
            run(key, &iv, encrypt, &mut output, &vec![1; input.len()]);
            assert_eq!(output, expected);
            for len in 0..input.len() {
                let mut output = input[..len].to_vec();
                run(key, &iv, encrypt, &mut output, &[]);
                assert_eq!(output, expected[..len]);
            }
        }
    }
}

/// Checks every vector of a response file, and returns how many there were.
fn check_file(text: &str, split: bool) -> usize {
    let mut count = 0;
    for fields in cavp_records(text) {
        check(
            &unhex(fields["KEY"]),
            &unhex(fields["IV"]),
            &unhex(fields["PLAINTEXT"]),
            &unhex(fields["CIPHERTEXT"]),
            split,
        );
        count += 1;
    }
    count
}

#[test]
fn nist_cfb8() {
    let files = [
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cfb8/CFB8GFSbox128.rsp"),
            14,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cfb8/CFB8GFSbox192.rsp"),
            12,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cfb8/CFB8GFSbox256.rsp"),
            10,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cfb8/CFB8KeySbox128.rsp"),
            42,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cfb8/CFB8KeySbox192.rsp"),
            48,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cfb8/CFB8KeySbox256.rsp"),
            32,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cfb8/CFB8VarKey128.rsp"),
            256,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cfb8/CFB8VarKey192.rsp"),
            384,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cfb8/CFB8VarKey256.rsp"),
            512,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cfb8/CFB8VarTxt128.rsp"),
            256,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cfb8/CFB8VarTxt192.rsp"),
            256,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cfb8/CFB8VarTxt256.rsp"),
            256,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-mmt/CFB8MMT128.rsp"),
            20,
            true,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-mmt/CFB8MMT192.rsp"),
            20,
            true,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-mmt/CFB8MMT256.rsp"),
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

#[test]
fn limits_and_lengths() {
    let iv = [0x3c; 16];
    for len in 0..=40 {
        let key: Vec<_> = crate::bytes::pattern(len, 17, 3);
        if !matches!(len, 16 | 24 | 32) {
            assert!(matches!(
                AesCfb8Encryptor::new(&key, &iv),
                Err(InvalidKeyLength)
            ));
            assert!(matches!(
                AesCfb8Decryptor::new(&key, &iv),
                Err(InvalidKeyLength)
            ));
            continue;
        }
        // Every length is a prefix of the longest message's ciphertext (to
        // which an empty first piece makes no difference), and round-trips.
        let message: Vec<_> = crate::bytes::pattern(16 * 5, 7, 1);
        let mut ciphertext = message.clone();
        run(&key, &iv, true, &mut ciphertext, &[0]);
        for n in 0..message.len() {
            let mut buffer = message[..n].to_vec();
            run(&key, &iv, true, &mut buffer, &[]);
            assert_eq!(buffer, ciphertext[..n]);
            run(&key, &iv, false, &mut buffer, &[0]);
            assert_eq!(buffer, message[..n]);
        }
    }
}
