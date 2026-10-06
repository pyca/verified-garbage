//! ECDSA over P-521 with SHA-512, and P-521 public keys, beside OpenSSL
//! and aws-lc-rs.

use criterion::Criterion;

pub const USES: &[&str] = &[
    "ecdsa_p521_sha512",
    "ecdsa_p521",
    "ec_p521",
    "hmac_sha512",
    "sha512",
];

/// For each hash function, signing a message: deterministically (RFC 6979),
/// and in OpenSSL and aws-lc-rs with a random `k` (their default; aws-lc-rs
/// has no deterministic signing); and verifying a signature, with the public
/// key decoded and checked in each verification, as the verified code does.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use aws_lc_rs::agreement::{ECDH_P521, PrivateKey};
    use aws_lc_rs::signature::{ECDSA_P521_SHA512_ASN1, ECDSA_P521_SHA512_FIXED_SIGNING};
    use criterion::BenchmarkId;
    use openssl::bn::{BigNum, BigNumContext};
    use openssl::ec::{EcGroup, EcPoint, PointConversionForm};
    use openssl::hash::MessageDigest;
    use openssl::nid::Nid;
    use verified_garbage::ecdsa::{P521, SigningKey};
    use verified_garbage::hashes::sha512::Sha512;

    use crate::{AWS_LC, OPENSSL, VG};

    // A key below P-521's order, whose top byte is at most 1.
    let mut d = [0x42; 66];
    d[0] = 1;
    hash::<Sha512>(
        c,
        "sha512",
        MessageDigest::sha512(),
        Some(&ECDSA_P521_SHA512_FIXED_SIGNING),
        &ECDSA_P521_SHA512_ASN1,
        &d,
    );

    // The public key of a private key, uncompressed: in OpenSSL, `[d]G` and
    // its encoding. The ids' size is the bytes of the public key.
    let group = EcGroup::from_curve_name(Nid::SECP521R1).unwrap();
    let mut ctx = BigNumContext::new().unwrap();
    let mut g = c.benchmark_group("ec_p521_public_key");
    g.bench_function(BenchmarkId::new(VG, 133), |b| {
        b.iter(|| {
            SigningKey::<P521>::from_bytes(black_box(&d))
                .public_key()
                .unwrap()
        })
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 133), |b| {
        b.iter(|| {
            let d = BigNum::from_slice(black_box(&d)).unwrap();
            let mut q = EcPoint::new(&group).unwrap();
            q.mul_generator2(&group, &d, &mut ctx).unwrap();
            q.to_bytes(&group, PointConversionForm::UNCOMPRESSED, &mut ctx)
                .unwrap()
        })
    });
    // aws-lc-rs computes the public key of a bare private key only for ECDH
    // (`agreement::PrivateKey`), when it constructs one.
    assert_eq!(
        PrivateKey::from_private_key(&ECDH_P521, &d)
            .unwrap()
            .compute_public_key()
            .unwrap()
            .as_ref(),
        SigningKey::<P521>::from_bytes(&d).public_key().unwrap()
    );
    g.bench_function(BenchmarkId::new(AWS_LC, 133), |b| {
        b.iter(|| {
            PrivateKey::from_private_key(&ECDH_P521, black_box(&d))
                .unwrap()
                .compute_public_key()
                .unwrap()
        })
    });
    g.finish();
}

/// Signing and verifying with the hash function `H`, named `name`, which
/// OpenSSL calls `md`, with the private key `d`; in aws-lc-rs, signing with
/// `aws_lc_sign` (`r ‖ s`, as the verified code does) if it signs with this
/// curve and hash, and verifying the DER signature OpenSSL verifies with
/// `aws_lc_verify`.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64"
))]
fn hash<H: verified_garbage::ecdsa::SignatureHash<verified_garbage::ecdsa::P521>>(
    c: &mut Criterion,
    name: &str,
    md: openssl::hash::MessageDigest,
    aws_lc_sign: Option<&'static aws_lc_rs::signature::EcdsaSigningAlgorithm>,
    aws_lc_verify: &'static aws_lc_rs::signature::EcdsaVerificationAlgorithm,
    d: &[u8; 66],
) {
    use std::hint::black_box;

    use aws_lc_rs::rand::SystemRandom;
    use aws_lc_rs::signature::{EcdsaKeyPair, UnparsedPublicKey};
    use criterion::BenchmarkId;
    use openssl::bn::{BigNum, BigNumContext};
    use openssl::ec::{EcGroup, EcKey, EcPoint};
    use openssl::ecdsa::EcdsaSig;
    use openssl::nid::Nid;
    use openssl::pkey::PKey;
    use openssl::sign::{Signer, Verifier};
    use verified_garbage::ecdsa::{P521, SigningKey, VerifyingKey};

    use crate::{AWS_LC, OPENSSL, SIZES, VG};

    let key = SigningKey::<P521>::from_bytes(d);
    let group = EcGroup::from_curve_name(Nid::SECP521R1).unwrap();
    let mut ctx = BigNumContext::new().unwrap();
    let d_bn = BigNum::from_slice(d).unwrap();
    let mut public = EcPoint::new(&group).unwrap();
    public.mul_generator2(&group, &d_bn, &mut ctx).unwrap();
    let openssl_key =
        PKey::from_ec_key(EcKey::from_private_components(&group, &d_bn, &public).unwrap()).unwrap();
    let q = key.public_key().unwrap();
    let verifying_key = VerifyingKey::<P521>::from_bytes(&q);
    let aws_lc_key =
        aws_lc_sign.map(|alg| EcdsaKeyPair::from_private_key_and_public_key(alg, d, &q).unwrap());
    // Ignored: aws-lc-rs draws `k` from AWS-LC's own generator.
    let rng = SystemRandom::new();

    let mut g = c.benchmark_group(format!("ecdsa_p521_{name}_sign"));
    for size in SIZES {
        let message = vec![0x5a; size];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| key.sign::<H>(black_box(&message)).unwrap())
        });
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                Signer::new(md, &openssl_key)
                    .unwrap()
                    .sign_oneshot_to_vec(black_box(&message))
                    .unwrap()
            })
        });
        if let Some(aws_lc_key) = &aws_lc_key {
            let sig = aws_lc_key.sign(&rng, &message).unwrap();
            verifying_key
                .verify::<H>(&message, sig.as_ref().try_into().unwrap())
                .unwrap();
            g.bench_function(BenchmarkId::new(AWS_LC, size), |b| {
                b.iter(|| aws_lc_key.sign(&rng, black_box(&message)).unwrap())
            });
        }
    }
    g.finish();

    let mut g = c.benchmark_group(format!("ecdsa_p521_{name}_verify"));
    for size in SIZES {
        let message = vec![0x5a; size];
        let sig = key.sign::<H>(&message).unwrap();
        let der = EcdsaSig::from_private_components(
            BigNum::from_slice(&sig[..66]).unwrap(),
            BigNum::from_slice(&sig[66..]).unwrap(),
        )
        .unwrap()
        .to_der()
        .unwrap();
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                verifying_key
                    .verify::<H>(black_box(&message), &sig)
                    .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let point = EcPoint::from_bytes(&group, black_box(&q), &mut ctx).unwrap();
                let ec = EcKey::from_public_key(&group, &point).unwrap();
                ec.check_key().unwrap();
                let pkey = PKey::from_ec_key(ec).unwrap();
                let mut verifier = Verifier::new(md, &pkey).unwrap();
                assert!(verifier.verify_oneshot(&der, black_box(&message)).unwrap());
            })
        });
        UnparsedPublicKey::new(aws_lc_verify, &q)
            .verify(&message, &der)
            .unwrap();
        g.bench_function(BenchmarkId::new(AWS_LC, size), |b| {
            b.iter(|| {
                UnparsedPublicKey::new(aws_lc_verify, black_box(&q))
                    .verify(black_box(&message), &der)
                    .unwrap()
            })
        });
    }
    g.finish();
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64"
)))]
pub fn bench(_: &mut Criterion) {}
