//! SM4-CTR: the CTR examples (A.2.5) of the Internet-Draft
//! draft-ribose-cfrg-sm4-10, unmodified under vectors/, whole, in pieces,
//! truncated, and in place in unaligned buffers; and, since neither is
//! longer than four blocks, the increment of the counter block across its
//! words and past `2¹²⁸` on longer messages, each block of a keystream being
//! the one its counter block gives alone (`tests/modes.rs`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::cipher::sm4::Sm4Ctr;

use super::{field, section};

/// The examples, both ways, truncated, in pieces and with a partial last
/// block (`crate::modes::check`).
#[test]
fn draft_examples() {
    for (from, to) in [
        ("A.2.5.1.  Example 1", "A.2.5.2.  Example 2"),
        ("A.2.5.2.  Example 2", "Appendix B.  Sample Implementation"),
    ] {
        let text = &section(from, to);
        let key: [u8; 16] = field(text, "Encryption key:").try_into().unwrap();
        let iv: [u8; 16] = field(text, "IV:").try_into().unwrap();
        let plaintext = field(text, "Plaintext:");
        let ciphertext = field(text, "Ciphertext:");
        for io in [(&plaintext[..], &ciphertext[..]), (&ciphertext, &plaintext)] {
            crate::modes::check(
                iv,
                io,
                &|c| Sm4Ctr::new(&key, c),
                Sm4Ctr::apply_keystream,
                Sm4Ctr::apply_keystream_final,
            );
        }
    }
}

/// The counter block's increment carries across its 32- and 64-bit words and
/// wraps from `1¹²⁸` to `0¹²⁸` (`crate::modes::check_counter`), on messages
/// of 15 and of 18 blocks (the code takes them in groups, then singly), at
/// aligned and unaligned addresses.
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
    let key: [u8; 16] = crate::bytes::pattern(16, 29, 7).try_into().unwrap();
    for start in starts {
        for blocks in [15, 18] {
            crate::modes::check_counter(
                start.to_be_bytes(),
                blocks,
                &|c| Sm4Ctr::new(&key, c),
                Sm4Ctr::apply_keystream,
                Sm4Ctr::apply_keystream_final,
            );
        }
    }
}

/// The examples in place, at every offset of the data, leave the bytes
/// around them unchanged.
#[test]
fn unaligned_buffers() {
    for (from, to) in [
        ("A.2.5.1.  Example 1", "A.2.5.2.  Example 2"),
        ("A.2.5.2.  Example 2", "Appendix B.  Sample Implementation"),
    ] {
        let text = &section(from, to);
        let key: [u8; 16] = field(text, "Encryption key:").try_into().unwrap();
        let iv: [u8; 16] = field(text, "IV:").try_into().unwrap();
        let plaintext = field(text, "Plaintext:");
        let ciphertext = field(text, "Ciphertext:");
        for io in [
            (&plaintext[..], &ciphertext[..]),
            (&ciphertext[..], &plaintext[..]),
        ] {
            crate::modes::check_unaligned(
                iv,
                io,
                &|iv| Sm4Ctr::new(&key, iv),
                Sm4Ctr::apply_keystream_final,
            );
        }
    }
}
