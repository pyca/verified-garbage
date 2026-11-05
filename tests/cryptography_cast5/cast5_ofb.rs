#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::error::InvalidKeyLength;

use verified_garbage::cast5_ofb::Cast5Ofb;

/// The vectors both ways, truncated, in pieces and with a partial last
/// block (`crate::modes::check`).
#[test]
fn vectors() {
    let records = super::records(&crate::vectors::text(
        "vectors/cryptography-cast5-ofb/cast5-ofb.txt",
    ));
    assert_eq!(records.len(), 20);
    for (key, iv, plaintext, ciphertext) in records {
        for io in [(&plaintext[..], &ciphertext[..]), (&ciphertext, &plaintext)] {
            crate::modes::check(
                iv,
                io,
                &|iv| Cast5Ofb::new(&key, iv).unwrap(),
                Cast5Ofb::apply_keystream,
                Cast5Ofb::apply_keystream_final,
            );
        }
    }
}

#[test]
fn errors() {
    assert_eq!(
        Cast5Ofb::new(&[0; 17], &[0; 8]).err(),
        Some(InvalidKeyLength)
    );
}
