//! The AES-CTR test vectors of RFC 3686 §6, read from the byte-for-byte
//! vendored RFC; and the increment of the counter block across its words and
//! past `2¹²⁸`, each block of a keystream being the one its counter block
//! gives alone (`tests/modes.rs`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::bytes::counter_add;
use crate::text::{get, labelled};
use verified_garbage::aes_ctr::AesCtr;
use verified_garbage::error::{IncompleteBlock, InvalidKeyLength};

/// Checks a message truncated, in pieces and with a partial last block
/// (`crate::modes::check`).
fn check(key: &[u8], ctr: &[u8; 16], input: &[u8], expected: &[u8]) {
    crate::modes::check(
        *ctr,
        (input, expected),
        &|c| AesCtr::new(key, c).unwrap(),
        AesCtr::apply_keystream,
        AesCtr::apply_keystream_final,
    );
}

#[test]
fn rfc3686_test_vectors() {
    // The section itself, not its line in the table of contents.
    let text = crate::vectors::text("vectors/rfc3686/rfc3686.txt");
    let section = text.rsplit_once("6.  Test Vectors").unwrap().1;
    let section = section.split_once("7.  Security Considerations").unwrap().0;
    let mut key_lens = Vec::new();
    for vector in section.split("Test Vector #").skip(1) {
        let fields = labelled(vector);
        let key = get(&fields, "aes key");
        let ctr: [u8; 16] = get(&fields, "counter block (1)").try_into().unwrap();
        let plaintext = get(&fields, "plaintext");
        let ciphertext = get(&fields, "ciphertext");
        key_lens.push(key.len());
        check(key, &ctr, plaintext, ciphertext);
        check(key, &ctr, ciphertext, plaintext);
        // The key stream is CTR of zeros, block by block from its counter block.
        let blocks = plaintext.len().div_ceil(16);
        let mut stream = vec![0; 16 * blocks];
        AesCtr::new(key, &ctr)
            .unwrap()
            .apply_keystream_final(&mut stream);
        for (j, block) in stream.chunks(16).enumerate() {
            assert_eq!(
                get(&fields, &format!("counter block ({})", j + 1)),
                counter_add(&ctr, j)
            );
            assert_eq!(get(&fields, &format!("key stream ({})", j + 1)), block);
        }
    }
    assert_eq!(key_lens, [16, 16, 16, 24, 24, 24, 32, 32, 32]);
}

/// The counter block's increment carries across its 32- and 64-bit words and
/// wraps from `1¹²⁸` to `0¹²⁸` (`crate::modes::check_counter`), on messages
/// of 5 blocks and a bit, at aligned and unaligned addresses.
#[test]
fn counter_carries_and_wraps() {
    let starts: [u128; 6] = [
        u128::MAX - 2,
        u128::MAX,
        (1 << 32) - 2,
        (1 << 64) - 3,
        (1 << 96) - 1,
        0x0123_4567_89ab_cdef_ffff_ffff_ffff_fffe,
    ];
    for key_len in [16, 24, 32] {
        let key: Vec<_> = crate::bytes::pattern(key_len, 29, 7);
        for start in starts {
            crate::modes::check_counter(
                start.to_be_bytes(),
                6,
                &|c| AesCtr::new(&key, c).unwrap(),
                AesCtr::apply_keystream,
                AesCtr::apply_keystream_final,
            );
        }
    }
}

#[test]
fn limits_and_lengths() {
    let ctr = [0x3c; 16];
    for len in 0..=40 {
        let key: Vec<_> = crate::bytes::pattern(len, 17, 3);
        if !matches!(len, 16 | 24 | 32) {
            assert!(matches!(AesCtr::new(&key, &ctr), Err(InvalidKeyLength)));
            continue;
        }
        // An empty call, and a refused one, change nothing.
        let mut ctx = AesCtr::new(&key, &ctr).unwrap();
        ctx.apply_keystream(&mut []).unwrap();
        let mut data = [0xa5; 20];
        assert_eq!(ctx.apply_keystream(&mut data), Err(IncompleteBlock));
        assert_eq!(data, [0xa5; 20]);
        let mut expected = data;
        AesCtr::new(&key, &ctr)
            .unwrap()
            .apply_keystream_final(&mut expected);
        ctx.apply_keystream_final(&mut data);
        assert_eq!(data, expected);
    }
}
