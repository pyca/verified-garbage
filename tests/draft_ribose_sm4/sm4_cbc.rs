//! SM4-CBC: the CBC examples (A.2.2) of the Internet-Draft
//! draft-ribose-cfrg-sm4-10, unmodified under vectors/, whole, in pieces,
//! and in place in unaligned buffers.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::sm4_cbc::{Error, Sm4Cbc};

use super::{field, section};

/// An example: key, IV, plaintext and ciphertext.
type Example = ([u8; 16], [u8; 16], Vec<u8>, Vec<u8>);

/// The examples.
fn examples() -> Vec<Example> {
    let mut examples = Vec::new();
    for (from, to) in [
        ("A.2.2.1.  Example 1", "A.2.2.2.  Example 2"),
        ("A.2.2.2.  Example 2", "A.2.3.  SM4-OFB Examples"),
    ] {
        let text = &section(from, to);
        examples.push((
            field(text, "Encryption Key:").try_into().unwrap(),
            field(text, "IV:").try_into().unwrap(),
            field(text, "Plaintext:"),
            field(text, "Ciphertext:"),
        ));
    }
    examples
}

/// `plaintext` encrypts to `ciphertext` and decrypts back, whole and split
/// at every block boundary, leaving the last ciphertext block as the
/// chaining value.
fn check(ctx: &Sm4Cbc, iv: [u8; 16], plaintext: &[u8], ciphertext: &[u8]) {
    let after: [u8; 16] = *ciphertext.last_chunk().unwrap();
    for offset in (0..=plaintext.len()).step_by(16) {
        let mut chain = iv;
        let mut buffer = plaintext.to_vec();
        ctx.encrypt(&mut chain, &mut buffer[..offset]).unwrap();
        ctx.encrypt(&mut chain, &mut buffer[offset..]).unwrap();
        assert_eq!(buffer, ciphertext);
        assert_eq!(chain, after);
        let mut chain = iv;
        ctx.decrypt(&mut chain, &mut buffer[..offset]).unwrap();
        ctx.decrypt(&mut chain, &mut buffer[offset..]).unwrap();
        assert_eq!(buffer, plaintext);
        assert_eq!(chain, after);
    }
}

#[test]
fn draft_examples() {
    for (key, iv, plaintext, ciphertext) in examples() {
        check(&Sm4Cbc::new(&key), iv, &plaintext, &ciphertext);
    }
}

#[test]
fn incomplete_blocks() {
    let ctx = Sm4Cbc::new(&[0; 16]);
    for len in [1, 15, 17, 31] {
        let mut chain = [7; 16];
        let mut buffer = vec![0x5a; len];
        assert_eq!(
            ctx.encrypt(&mut chain, &mut buffer),
            Err(Error::IncompleteBlock)
        );
        assert_eq!(
            ctx.decrypt(&mut chain, &mut buffer),
            Err(Error::IncompleteBlock)
        );
        assert_eq!(buffer, vec![0x5a; len]);
        assert_eq!(chain, [7; 16]);
    }
}

/// The examples in place, at every offset of the data and the chaining
/// value, leave the bytes around them unchanged.
#[test]
fn unaligned_guarded() {
    for (key, iv, plaintext, ciphertext) in examples() {
        let ctx = Sm4Cbc::new(&key);
        let after = ciphertext[ciphertext.len() - 16..].try_into().unwrap();
        crate::modes::check_unaligned(iv, (&plaintext, &ciphertext), after, &|iv, b| {
            ctx.encrypt(iv, b).unwrap()
        });
        crate::modes::check_unaligned(iv, (&ciphertext, &plaintext), after, &|iv, b| {
            ctx.decrypt(iv, b).unwrap()
        });
    }
}
