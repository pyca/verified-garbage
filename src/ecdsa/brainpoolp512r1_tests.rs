//! Tests of the verified brainpoolP512r1 signing and verification cores.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

extern crate std;

use crate::arch::ec_brainpoolp512r1::vg_ec_brainpoolp512r1_public_key;
use crate::arch::ecdsa_brainpoolp512r1::{
    vg_ecdsa_brainpoolp512r1_sign, vg_ecdsa_brainpoolp512r1_verify,
};
use crate::hashes::sha512::Sha512;

fn sign(d: &[u8; 64], digest: &[u8; 64], k: &[u8; 64]) -> (u32, [u8; 128]) {
    let mut signature = [0xa5; 128];
    let mut scratch = [0u64; 1024];
    // SAFETY: all buffers have the specified sizes; writable buffers are
    // separate Rust objects from all inputs and the call's stack frame.
    let ok = unsafe { vg_ecdsa_brainpoolp512r1_sign(&mut signature, d, digest, k, &mut scratch) };
    (ok, signature)
}

fn verify(q: &[u8; 129], digest: &[u8; 64], signature: &[u8; 128]) -> u32 {
    let mut scratch = [0u64; 1024];
    // SAFETY: scratch is a separate object from the correctly sized inputs
    // and the call's stack frame; no object wraps the address space.
    unsafe { vg_ecdsa_brainpoolp512r1_verify(q, digest, signature, &mut scratch) }
}

#[test]
fn sign_and_verify() {
    let d = [0x42; 64];
    let k = [0x24; 64];
    let mut q = [0; 129];
    let mut scratch = [0u64; 1024];
    // SAFETY: the buffers have the contracted sizes and are separate objects.
    assert_eq!(
        unsafe { vg_ec_brainpoolp512r1_public_key(&mut q, &d, &mut scratch) },
        1
    );
    for digest in [[0; 64], [0xff; 64], Sha512::digest(b"brainpoolP512r1 core")] {
        let (ok, signature) = sign(&d, &digest, &k);
        assert_eq!(ok, 1);
        assert_eq!(verify(&q, &digest, &signature), 1);
        let mut changed = signature;
        changed[127] ^= 1;
        assert_eq!(verify(&q, &digest, &changed), 0);
        let mut bad_q = q;
        bad_q[0] = 0;
        assert_eq!(verify(&bad_q, &digest, &signature), 0);
    }
    for invalid in [[0; 64], [0xff; 64]] {
        assert_eq!(sign(&invalid, &[0; 64], &k), (0, [0; 128]));
        assert_eq!(sign(&d, &[0; 64], &invalid), (0, [0; 128]));
    }
}

fn hex(s: &str) -> std::vec::Vec<u8> {
    assert_eq!(s.len() % 2, 0);
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

#[test]
fn wycheproof() {
    let Some(root) = std::env::var_os("WYCHEPROOF_ROOT") else {
        // CI always supplies the Wycheproof checkout.
        // NO-COVERAGE-START
        std::eprintln!("skipping: set WYCHEPROOF_ROOT to a C2SP/wycheproof checkout");
        return;
        // NO-COVERAGE-END
    };
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join(root)
        .join("testvectors_v1/ecdsa_brainpoolP512r1_sha512_p1363_test.json");
    let file: serde_json::Value = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
    let mut count = 0;
    let mut valid = 0;
    for group in file["testGroups"].as_array().unwrap() {
        assert_eq!(group["publicKey"]["curve"], "brainpoolP512r1");
        assert_eq!(group["sha"], "SHA-512");
        let q: [u8; 129] = hex(group["publicKey"]["uncompressed"].as_str().unwrap())
            .try_into()
            .unwrap();
        for test in group["tests"].as_array().unwrap() {
            count += 1;
            let expected = test["result"] == "valid";
            let signature = hex(test["sig"].as_str().unwrap());
            let Ok(signature) = <[u8; 128]>::try_from(signature.as_slice()) else {
                assert!(!expected);
                continue;
            };
            let digest = Sha512::digest(&hex(test["msg"].as_str().unwrap()));
            let tc_id = &test["tcId"];
            let result = verify(&q, &digest, &signature);
            assert_eq!(result, u32::from(expected), "tcId {tc_id}");
            valid += usize::from(expected);
        }
    }
    assert_eq!(count, file["numberOfTests"].as_u64().unwrap());
    assert!(valid > 0 && valid < count as usize);
}

/// Published Botan signatures with explicit nonces and raw 64-byte digests.
#[test]
fn botan_known_answers() {
    let text = include_str!("../../vectors/botan-ecdsa-prob/ecdsa_prob.vec");
    let group = text
        .split("Group = brainpool512r1\n")
        .nth(1)
        .unwrap()
        .split("Group =")
        .next()
        .unwrap();
    fn value<'a>(text: &'a str, label: &str) -> &'a str {
        text.lines()
            .find_map(|line| line.strip_prefix(label))
            .unwrap()
    }
    let d: [u8; 64] = hex(value(group, "X = 0x")).try_into().unwrap();
    let mut count = 0;
    for case in group
        .split("\n\n")
        .filter(|block| block.contains("Signature = "))
    {
        let digest = hex(value(case, "Msg = ")).try_into().unwrap();
        let nonce = hex(value(case, "Nonce = ")).try_into().unwrap();
        let signature = hex(value(case, "Signature = ")).try_into().unwrap();
        assert_eq!(sign(&d, &digest, &nonce), (1, signature));
        count += 1;
    }
    assert_eq!(count, 8);
}
