//! Triple DES-CFB64: NIST CAVP's multi-block message tests, unmodified under
//! vectors/, truncated and split (`tests/modes.rs`), for each key length.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::triple_des_cfb::{InvalidKeyLength, TripleDesCfb64};

use verified_garbage_test_vectors::{cavp_records, unhex};

/// `plaintext` encrypts to `ciphertext` and decrypts back, truncated and
/// split (`crate::modes::check`).
fn check(ctx: &TripleDesCfb64, iv: [u8; 8], plaintext: &[u8], ciphertext: &[u8]) {
    let vector = (plaintext, ciphertext);
    let cfb = crate::modes::Feedback::Ciphertext;
    crate::modes::check(cfb, iv, vector, vector, &|iv, b| ctx.encrypt(iv, b));
    crate::modes::check(cfb, iv, vector, (ciphertext, plaintext), &|iv, b| {
        ctx.decrypt(iv, b)
    });
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
            &TripleDesCfb64::new(&key).unwrap(),
            iv,
            &plaintext,
            &ciphertext,
        );
        if key[..8] == key[16..] {
            check(
                &TripleDesCfb64::new(&key[..16]).unwrap(),
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
            "vectors/nist-cavp-tdes-mmt/TCFB64MMT2.rsp"
        )),
        10
    );
    assert_eq!(
        check_file(&crate::vectors::text(
            "vectors/nist-cavp-tdes-mmt/TCFB64MMT3.rsp"
        )),
        20
    );
}

#[test]
fn errors() {
    for len in [0, 8, 15, 17, 32] {
        assert_eq!(
            TripleDesCfb64::new(&vec![0; len]).err(),
            Some(InvalidKeyLength)
        );
    }
}
