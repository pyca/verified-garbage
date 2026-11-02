//! Triple DES-CFB8: NIST CAVP's multi-block message tests, unmodified under
//! vectors/, whole and split at every byte, for each key length.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::triple_des_cfb8::{InvalidKeyLength, TripleDesCfb8};

use verified_garbage_test_vectors::{cavp_records, unhex};

/// `plaintext` encrypts to `ciphertext` and decrypts back, whole and split
/// at every byte, leaving the shift register holding the last eight bytes
/// of the IV and the ciphertext.
fn check(ctx: &TripleDesCfb8, iv: [u8; 8], plaintext: &[u8], ciphertext: &[u8]) {
    let register = [&iv[..], ciphertext].concat();
    let next: [u8; 8] = register[register.len() - 8..].try_into().unwrap();
    for offset in 0..=plaintext.len() {
        let mut chain = iv;
        let mut buffer = plaintext.to_vec();
        ctx.encrypt(&mut chain, &mut buffer[..offset]);
        ctx.encrypt(&mut chain, &mut buffer[offset..]);
        assert_eq!(buffer, ciphertext);
        assert_eq!(chain, next);
        let mut chain = iv;
        ctx.decrypt(&mut chain, &mut buffer[..offset]);
        ctx.decrypt(&mut chain, &mut buffer[offset..]);
        assert_eq!(buffer, plaintext);
        assert_eq!(chain, next);
    }
}

fn check_file(text: &str) -> usize {
    let mut count = 0;
    for fields in cavp_records(text) {
        let mut key = unhex(fields["KEY1"]);
        key.extend(unhex(fields["KEY2"]));
        key.extend(unhex(fields["KEY3"]));
        let iv: [u8; 8] = unhex(fields["IV"]).try_into().unwrap();
        let plaintext = unhex(fields["PLAINTEXT"]);
        let ciphertext = unhex(fields["CIPHERTEXT"]);
        check(
            &TripleDesCfb8::new(&key).unwrap(),
            iv,
            &plaintext,
            &ciphertext,
        );
        if key[..8] == key[16..] {
            check(
                &TripleDesCfb8::new(&key[..16]).unwrap(),
                iv,
                &plaintext,
                &ciphertext,
            );
        }
        count += 1;
    }
    count
}

#[test]
fn cavp_mmt() {
    assert_eq!(
        check_file(&crate::vectors::text(
            "vectors/nist-cavp-tdes-mmt/TCFB8MMT2.rsp"
        )),
        10
    );
    assert_eq!(
        check_file(&crate::vectors::text(
            "vectors/nist-cavp-tdes-mmt/TCFB8MMT3.rsp"
        )),
        20
    );
}

#[test]
fn errors() {
    for len in [0, 8, 15, 17, 32] {
        assert_eq!(
            TripleDesCfb8::new(&vec![0; len]).err(),
            Some(InvalidKeyLength)
        );
    }
}
