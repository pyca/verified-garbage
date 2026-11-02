//! Triple DES-OFB: NIST CAVP's multi-block message tests, unmodified under
//! vectors/, truncated and split (`tests/modes.rs`), for each key length.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::triple_des_ofb::{InvalidKeyLength, TripleDesOfb};

use verified_garbage_test_vectors::{cavp_records, unhex};

fn check_file(text: &str) -> usize {
    let mut count = 0;
    for fields in cavp_records(text) {
        let mut key = unhex(fields["KEY1"]);
        key.extend(unhex(fields["KEY2"]));
        key.extend(unhex(fields["KEY3"]));
        let iv: [u8; 8] = unhex(fields["IV"]).try_into().unwrap();
        let plaintext = unhex(fields["PLAINTEXT"]);
        let ciphertext = unhex(fields["CIPHERTEXT"]);
        let mut keys = vec![key.clone()];
        if key[..8] == key[16..] {
            keys.push(key[..16].to_vec());
        }
        for key in keys {
            let ctx = TripleDesOfb::new(&key).unwrap();
            let vector = (&plaintext[..], &ciphertext[..]);
            for io in [vector, (&ciphertext[..], &plaintext[..])] {
                crate::modes::check(crate::modes::Feedback::Output, iv, vector, io, &|iv, b| {
                    ctx.apply_keystream(iv, b)
                });
            }
        }
        count += 1;
    }
    count
}

#[test]
fn cavp_mmt() {
    assert_eq!(
        check_file(&crate::vectors::text(
            "vectors/nist-cavp-tdes-mmt/TOFBMMT2.rsp"
        )),
        10
    );
    assert_eq!(
        check_file(&crate::vectors::text(
            "vectors/nist-cavp-tdes-mmt/TOFBMMT3.rsp"
        )),
        20
    );
}

#[test]
fn errors() {
    for len in [0, 8, 15, 17, 32] {
        assert_eq!(
            TripleDesOfb::new(&vec![0; len]).err(),
            Some(InvalidKeyLength)
        );
    }
}
