//! NIST CAVP AES-CFB128 known-answer (KAT) and multi-block message (MMT)
//! vectors, with unmodified sources under vectors/.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::error::{IncompleteBlock, InvalidKeyLength};

use verified_garbage::aes_cfb::{AesCfb128Decryptor, AesCfb128Encryptor};

use verified_garbage_test_vectors::{cavp_records, unhex};

/// Checks a vector in both directions, in one call; with `split`, also
/// truncated (with a partial last segment) and in pieces
/// (`crate::modes::check`).
fn check(key: &[u8], iv: &[u8], plaintext: &[u8], ciphertext: &[u8], split: bool) {
    assert_eq!(plaintext.len(), ciphertext.len());
    assert_eq!(plaintext.len() % 16, 0);
    let iv: [u8; 16] = iv.try_into().unwrap();
    let encryptor = |iv: &[u8; 16]| AesCfb128Encryptor::new(key, iv).unwrap();
    let decryptor = |iv: &[u8; 16]| AesCfb128Decryptor::new(key, iv).unwrap();
    if split {
        crate::modes::check(
            iv,
            (plaintext, ciphertext),
            &encryptor,
            AesCfb128Encryptor::encrypt,
            AesCfb128Encryptor::encrypt_final,
        );
        crate::modes::check(
            iv,
            (ciphertext, plaintext),
            &decryptor,
            AesCfb128Decryptor::decrypt,
            AesCfb128Decryptor::decrypt_final,
        );
    } else {
        let mut output = plaintext.to_vec();
        encryptor(&iv).encrypt(&mut output).unwrap();
        assert_eq!(output, ciphertext);
        decryptor(&iv).decrypt_final(&mut output);
        assert_eq!(output, plaintext);
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
fn nist_cfb128() {
    let files = [
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cfb128/CFB128GFSbox128.rsp"),
            14,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cfb128/CFB128GFSbox192.rsp"),
            12,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cfb128/CFB128GFSbox256.rsp"),
            10,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cfb128/CFB128KeySbox128.rsp"),
            42,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cfb128/CFB128KeySbox192.rsp"),
            48,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cfb128/CFB128KeySbox256.rsp"),
            32,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cfb128/CFB128VarKey128.rsp"),
            256,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cfb128/CFB128VarKey192.rsp"),
            384,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cfb128/CFB128VarKey256.rsp"),
            512,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cfb128/CFB128VarTxt128.rsp"),
            256,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cfb128/CFB128VarTxt192.rsp"),
            256,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-cfb128/CFB128VarTxt256.rsp"),
            256,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-mmt/CFB128MMT128.rsp"),
            20,
            true,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-mmt/CFB128MMT192.rsp"),
            20,
            true,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-mmt/CFB128MMT256.rsp"),
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
                AesCfb128Encryptor::new(&key, &iv),
                Err(InvalidKeyLength)
            ));
            assert!(matches!(
                AesCfb128Decryptor::new(&key, &iv),
                Err(InvalidKeyLength)
            ));
            continue;
        }
        // An empty call and a refused one change nothing: every length is a
        // prefix of the longest message's output after them, and
        // round-trips. Every length below 35 blocks, partial segments
        // included, each decrypted in place at an offset of its length modulo
        // 16, with guards.
        let mut encryptor = AesCfb128Encryptor::new(&key, &iv).unwrap();
        encryptor.encrypt(&mut []).unwrap();
        let mut odd = [0x5a; 17];
        assert_eq!(encryptor.encrypt(&mut odd), Err(IncompleteBlock));
        assert_eq!(odd, [0x5a; 17]);
        let message: Vec<_> = crate::bytes::pattern(16 * 34 + 16, 7, 1);
        let mut ciphertext = message.clone();
        encryptor.encrypt_final(&mut ciphertext);
        for n in 0..message.len() {
            let mut buffer = message[..n].to_vec();
            AesCfb128Encryptor::new(&key, &iv)
                .unwrap()
                .encrypt_final(&mut buffer);
            assert_eq!(buffer, ciphertext[..n]);
            let offset = n % 16;
            let mut guarded = vec![0xa5; offset + n + 16];
            guarded[offset..offset + n].copy_from_slice(&buffer);
            AesCfb128Decryptor::new(&key, &iv)
                .unwrap()
                .decrypt_final(&mut guarded[offset..offset + n]);
            assert_eq!(guarded[offset..offset + n], message[..n]);
            assert!(crate::bytes::all_equal(&guarded[..offset], 0xa5));
            assert!(crate::bytes::all_equal(&guarded[offset + n..], 0xa5));
        }
    }
}
