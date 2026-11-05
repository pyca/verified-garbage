//! NIST CAVP AES-OFB known-answer (KAT) and multi-block message (MMT)
//! vectors, with unmodified sources under vectors/.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::aes_ofb::{AesOfb, Error};

use verified_garbage_test_vectors::{cavp_records, unhex};

/// Checks a vector in both directions, in one call; with `split`, also
/// truncated (with a partial last block) and in pieces
/// (`crate::modes::check`).
fn check(key: &[u8], iv: &[u8], plaintext: &[u8], ciphertext: &[u8], split: bool) {
    assert_eq!(plaintext.len(), ciphertext.len());
    assert_eq!(plaintext.len() % 16, 0);
    let iv: [u8; 16] = iv.try_into().unwrap();
    let encryptor = |iv: &[u8; 16]| AesOfb::new(key, iv).unwrap();
    let decryptor = |iv: &[u8; 16]| AesOfb::new(key, iv).unwrap();
    if split {
        crate::modes::check(
            iv,
            (plaintext, ciphertext),
            &encryptor,
            AesOfb::apply_keystream,
            AesOfb::apply_keystream_final,
        );
        crate::modes::check(
            iv,
            (ciphertext, plaintext),
            &decryptor,
            AesOfb::apply_keystream,
            AesOfb::apply_keystream_final,
        );
    } else {
        let mut output = plaintext.to_vec();
        encryptor(&iv).apply_keystream(&mut output).unwrap();
        assert_eq!(output, ciphertext);
        decryptor(&iv).apply_keystream_final(&mut output);
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
fn nist_ofb() {
    let files = [
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-ofb/OFBGFSbox128.rsp"),
            14,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-ofb/OFBGFSbox192.rsp"),
            12,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-ofb/OFBGFSbox256.rsp"),
            10,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-ofb/OFBKeySbox128.rsp"),
            42,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-ofb/OFBKeySbox192.rsp"),
            48,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-ofb/OFBKeySbox256.rsp"),
            32,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-ofb/OFBVarKey128.rsp"),
            256,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-ofb/OFBVarKey192.rsp"),
            384,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-ofb/OFBVarKey256.rsp"),
            512,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-ofb/OFBVarTxt128.rsp"),
            256,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-ofb/OFBVarTxt192.rsp"),
            256,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-kat-ofb/OFBVarTxt256.rsp"),
            256,
            false,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-mmt/OFBMMT128.rsp"),
            20,
            true,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-mmt/OFBMMT192.rsp"),
            20,
            true,
        ),
        (
            &crate::vectors::text("vectors/nist-cavp-aes-mmt/OFBMMT256.rsp"),
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
                AesOfb::new(&key, &iv),
                Err(Error::InvalidKeyLength)
            ));
            continue;
        }
        // An empty call and a refused one change nothing: every length is a
        // prefix of the longest message's output after them, and
        // round-trips. Every length below 35 blocks, partial blocks
        // included, each decrypted in place at an offset of its length modulo
        // 16, with guards.
        let mut encryptor = AesOfb::new(&key, &iv).unwrap();
        encryptor.apply_keystream(&mut []).unwrap();
        let mut odd = [0x5a; 17];
        assert_eq!(
            encryptor.apply_keystream(&mut odd),
            Err(Error::IncompleteBlock)
        );
        assert_eq!(odd, [0x5a; 17]);
        let message: Vec<_> = crate::bytes::pattern(16 * 34 + 16, 7, 1);
        let mut ciphertext = message.clone();
        encryptor.apply_keystream_final(&mut ciphertext);
        for n in 0..message.len() {
            let mut buffer = message[..n].to_vec();
            AesOfb::new(&key, &iv)
                .unwrap()
                .apply_keystream_final(&mut buffer);
            assert_eq!(buffer, ciphertext[..n]);
            let offset = n % 16;
            let mut guarded = vec![0xa5; offset + n + 16];
            guarded[offset..offset + n].copy_from_slice(&buffer);
            AesOfb::new(&key, &iv)
                .unwrap()
                .apply_keystream_final(&mut guarded[offset..offset + n]);
            assert_eq!(guarded[offset..offset + n], message[..n]);
            assert!(crate::bytes::all_equal(&guarded[..offset], 0xa5));
            assert!(crate::bytes::all_equal(&guarded[offset + n..], 0xa5));
        }
    }
}
