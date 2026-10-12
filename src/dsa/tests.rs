use super::*;
use crate::hashes::{sha1::Sha1, sha224::Sha224, sha256::Sha256, sha384::Sha384, sha512::Sha512};
use alloc::{format, string::ToString};

#[path = "../../tests/cavp/dsa_vectors.rs"]
mod vectors;
use vectors::{hex, vectors};

fn digest(hash: &str, msg: &[u8]) -> Vec<u8> {
    let hashes: [(&str, Vec<u8>); 5] = [
        ("SHA-1", Sha1::digest(msg).to_vec()),
        ("SHA-224", Sha224::digest(msg).to_vec()),
        ("SHA-256", Sha256::digest(msg).to_vec()),
        ("SHA-384", Sha384::digest(msg).to_vec()),
        ("SHA-512", Sha512::digest(msg).to_vec()),
    ];
    hashes
        .into_iter()
        .find(|(name, _)| *name == hash)
        .unwrap()
        .1
}

fn sample() -> (PrivateKey, Vec<u8>, Vec<u8>) {
    let cases = vectors(include_str!("../../vectors/nist-cavp-dsa/SigGen.txt"), true);
    let v = &cases[0];
    let p = hex(&v["P"], 0);
    let q = hex(&v["Q"], 0);
    let key = PrivateKey::from_components(
        &p,
        &q,
        &hex(&v["G"], p.len()),
        &hex(&v["Y"], p.len()),
        &hex(&v["X"], q.len()),
    )
    .unwrap();
    (
        key,
        digest(&v["Hash"], &hex(&v["Msg"], 0)),
        hex(&v["K"], q.len()),
    )
}

#[test]
fn cavp_signatures() {
    for (i, v) in vectors(include_str!("../../vectors/nist-cavp-dsa/SigGen.txt"), true)
        .iter()
        .enumerate()
    {
        let p = hex(&v["P"], 0);
        let q = hex(&v["Q"], 0);
        let key = PrivateKey::from_components(
            &p,
            &q,
            &hex(&v["G"], p.len()),
            &hex(&v["Y"], p.len()),
            &hex(&v["X"], q.len()),
        )
        .unwrap();
        let digest = digest(&v["Hash"], &hex(&v["Msg"], 0));
        let mut signature = vec![0xa5; 2 * q.len()];
        let mut scratch = Secret(vec![0xa5a5a5a5a5a5a5a5; 16 * p.len()]);
        assert!(
            key.sign_once(
                &digest,
                &hex(&v["K"], q.len()),
                &mut signature,
                &mut scratch.0
            ),
            "vector {i}"
        );
        let expected = [hex(&v["R"], q.len()), hex(&v["S"], q.len())].concat();
        assert_eq!(signature, expected, "vector {i}");
        assert!(key.public_key().verify(&digest, &signature), "vector {i}");
    }
}

#[test]
fn random_signing_and_digest_lengths() {
    let (key, _, _) = sample();
    for digest in [
        vec![],
        vec![3],
        vec![7; 19],
        vec![11; 20],
        vec![13; 64],
        vec![17; 129],
    ] {
        let signature = key.sign(&digest).unwrap();
        assert!(key.public_key().verify(&digest, &signature));
        assert!(!key.public_key().verify(&[21; 32], &signature));
    }
    assert!(!key.public_key().verify(&[], &[]));
    assert!(!key.public_key().verify(&[], &[0; 40]));
    assert!(format!("{key:?}").contains("PrivateKey"));
    assert!(format!("{:?}", key.public_key().clone()).contains("PublicKey"));
}

#[test]
fn padded_domain_and_scalars() {
    let cases = vectors(include_str!("../../vectors/nist-cavp-dsa/SigGen.txt"), true);
    let v = &cases[0];
    let digest = digest(&v["Hash"], &hex(&v["Msg"], 0));
    let p = hex(&v["P"], 256);
    let q = hex(&v["Q"], 32);
    let g = hex(&v["G"], 256);
    let y = hex(&v["Y"], 256);
    let x = hex(&v["X"], 32);
    let padded = PrivateKey::from_components(&p, &q, &g, &y, &x).unwrap();
    let mut output = vec![0xa5; 64];
    let mut scratch = Secret(vec![0xa5a5a5a5a5a5a5a5; 4096]);
    assert!(padded.sign_once(&digest, &hex(&v["K"], 32), &mut output, &mut scratch.0));
    assert!(padded.public_key().verify(&digest, &output));
    let fresh = padded.sign(&digest).unwrap();
    assert!(padded.public_key().verify(&digest, &fresh));
}

#[test]
fn malformed_keys_nonces_and_bounded_retries() {
    let (mut key, digest, nonce) = sample();
    let mut output = vec![0xa5; 40];
    let mut scratch = Secret(vec![0xa5a5a5a5a5a5a5a5; 2048]);
    for invalid in [vec![0; 20], key.public.packed[128..148].to_vec()] {
        assert!(!key.sign_once(&digest, &invalid, &mut output, &mut scratch.0));
        assert_eq!(output, vec![0; 40]);
    }
    assert_eq!(
        key.sign_with_rng(&digest, |_| Err(Error::Randomness)),
        Err(Error::Randomness)
    );
    let mut draws = 0;
    assert_eq!(
        key.sign_with_rng(&digest, |b| {
            b.fill(0);
            draws += 1;
            Ok(())
        }),
        Err(Error::InvalidKeyOrNonce)
    );
    assert_eq!(draws, 128);
    key.packed.0[404..].fill(0);
    draws = 0;
    assert_eq!(
        key.sign_with_rng(&digest, |b| {
            b.copy_from_slice(&nonce);
            draws += 1;
            Ok(())
        }),
        Err(Error::InvalidKeyOrNonce)
    );
    assert_eq!(draws, 8);
    key.public.packed[128..148].fill(0);
    assert_eq!(
        key.sign_with_rng(&digest, |_| panic!("zero q needs no RNG")),
        Err(Error::InvalidKeyOrNonce)
    );
    // Malformed public shape takes the early failure path and zeros output.
    key.packed.0[127] &= 0xfe;
    output.fill(0xa5);
    assert!(!key.sign_once(&digest, &nonce, &mut output, &mut scratch.0));
    assert_eq!(output, vec![0; 40]);
    assert!(!key.public_key().verify(&digest, &output));
}

#[test]
fn import_lengths_errors_and_backends() {
    assert_eq!(
        PublicKey::from_components(&[], &[], &[], &[]).unwrap_err(),
        Error::Length
    );
    assert_eq!(
        PublicKey::from_components(&[0; 128], &[0; 20], &[], &[0; 128]).unwrap_err(),
        Error::Length
    );
    assert_eq!(
        PublicKey::from_components(&[0; 128], &[0; 20], &[0; 128], &[]).unwrap_err(),
        Error::Length
    );
    assert_eq!(
        PrivateKey::from_components(&[], &[], &[], &[], &[]).unwrap_err(),
        Error::Length
    );
    assert_eq!(
        PrivateKey::from_components(&[0; 128], &[0; 20], &[0; 128], &[0; 128], &[]).unwrap_err(),
        Error::Length
    );
    assert_eq!(Backend::select(Features::of(&[])), Backend::Baseline);
    assert_eq!(Backend::select(Features::of(&["bmi2"])), Backend::Baseline);
    assert_eq!(
        Backend::select(Features::of(&["bmi2", "adx"])),
        Backend::Adx
    );
    for error in [Error::Length, Error::InvalidKeyOrNonce, Error::Randomness] {
        assert!(!error.to_string().is_empty());
        assert!(!format!("{error:?}").is_empty());
    }
}

#[test]
fn nonce_range_comparison() {
    for q in [1u16, 255, 256, 257, 65535] {
        for k in [0u16, 1, 254, 255, 256, 257, 65534, 65535] {
            assert_eq!(
                nonce_in_range(&k.to_be_bytes(), &q.to_be_bytes()),
                k != 0 && k < q
            );
        }
    }
}
