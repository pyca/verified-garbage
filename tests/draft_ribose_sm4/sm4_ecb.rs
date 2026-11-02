//! SM4 ECB: Appendix A of the Internet-Draft draft-ribose-cfrg-sm4-10, unmodified
//! under vectors/ (its round keys and intermediate values are checked in
//! `lean/VerifiedGarbageTest/Sm4.lean`). Its single blocks and its repeated
//! encryptions (A.1) and its ECB examples (A.2.1); its CBC, OFB, CFB and CTR
//! examples (A.2.2–A.2.5) are in `sm4_cbc.rs`, `sm4_ofb.rs`, `sm4_cfb.rs`
//! and `sm4_ctr.rs`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::sm4_ecb::{Error, Sm4Ecb};

use super::{field, section};

struct Example {
    key: [u8; 16],
    plaintext: Vec<u8>,
    ciphertext: Vec<u8>,
}

fn example(text: &str) -> Example {
    Example {
        key: field(text, "Encryption key:").try_into().unwrap(),
        plaintext: field(text, "Plaintext:"),
        ciphertext: field(text, "Ciphertext:"),
    }
}

/// ECB in both directions, whole and split at every block boundary.
fn check_ecb(key: &[u8; 16], plaintext: &[u8], ciphertext: &[u8]) {
    assert_eq!(plaintext.len(), ciphertext.len());
    let ctx = Sm4Ecb::new(key);
    for (operation, input, expected) in [
        (
            Sm4Ecb::encrypt as fn(&Sm4Ecb, &mut [u8]) -> Result<(), Error>,
            plaintext,
            ciphertext,
        ),
        (
            Sm4Ecb::decrypt as fn(&Sm4Ecb, &mut [u8]) -> Result<(), Error>,
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
fn single_blocks() {
    for (from, to) in [
        ("A.1.1.  Example 1 (", "A.1.2.  Example 2 ("),
        ("A.1.4.  Example 4", "A.1.5.  Example 5"),
    ] {
        let e = example(&section(from, to));
        check_ecb(&e.key, &e.plaintext, &e.ciphertext);
    }
    // Examples 2 and 5 decrypt examples 1 and 4: their "plaintext" is the
    // ciphertext and their "ciphertext" the plaintext.
    for (from, to) in [
        ("A.1.2.  Example 2 (", "A.1.3.  Example 3 ("),
        ("A.1.5.  Example 5", "A.1.6.  Example 6"),
    ] {
        let text = &section(from, to);
        let key: [u8; 16] = field(text, "Encryption key:").try_into().unwrap();
        check_ecb(
            &key,
            &field(text, "Plaintext:"),
            &field(text, "Ciphertext:"),
        );
    }
}

/// A block encrypted 1,000,000 times, sixteen copies at a time
/// (`decrypt`: the whole buffer of ciphertexts decrypted back as many
/// times). The two directions and the two examples run independently.
fn repeated(from: &str, to: &str, decrypt: bool) {
    let e = example(&section(from, to));
    let ctx = Sm4Ecb::new(&e.key);
    let (input, expected) = if decrypt {
        (&e.ciphertext, &e.plaintext)
    } else {
        (&e.plaintext, &e.ciphertext)
    };
    let mut buffer = input.repeat(16);
    for _ in 0..1_000_000 {
        if decrypt {
            ctx.decrypt(&mut buffer).unwrap();
        } else {
            ctx.encrypt(&mut buffer).unwrap();
        }
    }
    assert_eq!(buffer, expected.repeat(16));
}

#[test]
fn repeated_example_3_encrypt() {
    repeated("A.1.3.  Example 3 (", "A.1.4.  Example 4", false);
}

#[test]
fn repeated_example_3_decrypt() {
    repeated("A.1.3.  Example 3 (", "A.1.4.  Example 4", true);
}

#[test]
fn repeated_example_6_encrypt() {
    repeated(
        "A.1.6.  Example 6",
        "A.2.  Examples For Various Modes",
        false,
    );
}

#[test]
fn repeated_example_6_decrypt() {
    repeated(
        "A.1.6.  Example 6",
        "A.2.  Examples For Various Modes",
        true,
    );
}

#[test]
fn ecb() {
    for (from, to) in [
        ("A.2.1.1.  Example 1", "A.2.1.2.  Example 2"),
        ("A.2.1.2.  Example 2", "A.2.2.  SM4-CBC Examples"),
    ] {
        let e = example(&section(from, to));
        check_ecb(&e.key, &e.plaintext, &e.ciphertext);
        // The same blocks many times over.
        check_ecb(&e.key, &e.plaintext.repeat(21), &e.ciphertext.repeat(21));
    }
}

/// ECB of buffers at every offset modulo 8.
#[test]
fn unaligned_data() {
    let e = example(&section("A.2.1.2.  Example 2", "A.2.2.  SM4-CBC Examples"));
    let ctx = Sm4Ecb::new(&e.key);
    for offset in 0..8 {
        let mut buffer = vec![0; offset + e.plaintext.len()];
        buffer[offset..].copy_from_slice(&e.plaintext);
        ctx.encrypt(&mut buffer[offset..]).unwrap();
        assert_eq!(buffer[offset..], e.ciphertext[..]);
        ctx.decrypt(&mut buffer[offset..]).unwrap();
        assert_eq!(buffer[offset..], e.plaintext[..]);
    }
}

#[test]
fn incomplete_block() {
    let ctx = Sm4Ecb::new(&[0; 16]);
    for len in [1, 15, 17, 31] {
        let mut buffer = vec![0x5a; len];
        assert_eq!(ctx.encrypt(&mut buffer), Err(Error::IncompleteBlock));
        assert_eq!(ctx.decrypt(&mut buffer), Err(Error::IncompleteBlock));
        assert_eq!(buffer, vec![0x5a; len]);
    }
}
