//! ECDSA over secp256k1 with SHA-256, and secp256k1 public keys, beside OpenSSL.

use criterion::Criterion;

pub const USES: &[&str] = &[
    "ecdsa_secp256k1_sha256",
    "ecdsa_secp256k1",
    "ec_secp256k1",
    "hmac_sha256",
    "sha256",
];

/// For each hash function, signing a message: deterministically (RFC 6979),
/// and in OpenSSL with a random `k` (its default); and verifying a
/// signature, with the public key decoded and checked in each verification,
/// as the verified code does.
#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use openssl::bn::{BigNum, BigNumContext};
    use openssl::ec::{EcGroup, EcPoint, PointConversionForm};
    use openssl::hash::MessageDigest;
    use openssl::nid::Nid;
    use verified_garbage::ecdsa::{Secp256k1, SigningKey};
    use verified_garbage::hashes::sha256::Sha256;

    use crate::{OPENSSL, VG};

    let d = [0x42; 32];
    hash::<Sha256>(c, "sha256", MessageDigest::sha256(), &d);

    // The public key of a private key, uncompressed: in OpenSSL, `[d]G` and
    // its encoding. The ids' size is the bytes of the public key.
    let group = EcGroup::from_curve_name(Nid::SECP256K1).unwrap();
    let mut ctx = BigNumContext::new().unwrap();
    let mut g = c.benchmark_group("ec_secp256k1_public_key");
    g.bench_function(BenchmarkId::new(VG, 65), |b| {
        b.iter(|| {
            SigningKey::<Secp256k1>::from_bytes(black_box(&d))
                .public_key()
                .unwrap()
        })
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 65), |b| {
        b.iter(|| {
            let d = BigNum::from_slice(black_box(&d)).unwrap();
            let mut q = EcPoint::new(&group).unwrap();
            q.mul_generator2(&group, &d, &mut ctx).unwrap();
            q.to_bytes(&group, PointConversionForm::UNCOMPRESSED, &mut ctx)
                .unwrap()
        })
    });
    g.finish();
}

/// Signing and verifying with the hash function `H`, named `name`, which
/// OpenSSL calls `md`, with the private key `d`.
#[cfg(target_arch = "x86_64")]
fn hash<H: verified_garbage::ecdsa::SignatureHash<verified_garbage::ecdsa::Secp256k1>>(
    c: &mut Criterion,
    name: &str,
    md: openssl::hash::MessageDigest,
    d: &[u8; 32],
) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use openssl::bn::{BigNum, BigNumContext};
    use openssl::ec::{EcGroup, EcKey, EcPoint};
    use openssl::ecdsa::EcdsaSig;
    use openssl::nid::Nid;
    use openssl::pkey::PKey;
    use openssl::sign::{Signer, Verifier};
    use verified_garbage::ecdsa::{Secp256k1, SigningKey, VerifyingKey};

    use crate::{OPENSSL, SIZES, VG};

    let key = SigningKey::<Secp256k1>::from_bytes(d);
    let group = EcGroup::from_curve_name(Nid::SECP256K1).unwrap();
    let mut ctx = BigNumContext::new().unwrap();
    let d_bn = BigNum::from_slice(d).unwrap();
    let mut public = EcPoint::new(&group).unwrap();
    public.mul_generator2(&group, &d_bn, &mut ctx).unwrap();
    let openssl_key =
        PKey::from_ec_key(EcKey::from_private_components(&group, &d_bn, &public).unwrap()).unwrap();

    let mut g = c.benchmark_group(format!("ecdsa_secp256k1_{name}_sign"));
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
    }
    g.finish();

    let q = key.public_key().unwrap();
    let verifying_key = VerifyingKey::<Secp256k1>::from_bytes(&q);
    let digest = H::digest(&[0x5a; 32]);
    let ec_private = openssl_key.ec_key().unwrap();
    let mut g = c.benchmark_group(format!("ecdsa_secp256k1_{name}_sign_prehashed"));
    g.bench_function(BenchmarkId::new(VG, H::OUTPUT_SIZE), |b| {
        b.iter(|| key.sign_prehashed::<H>(black_box(&digest)).unwrap())
    });
    g.bench_function(BenchmarkId::new(OPENSSL, H::OUTPUT_SIZE), |b| {
        b.iter(|| EcdsaSig::sign(black_box(digest.as_ref()), &ec_private).unwrap())
    });
    g.finish();

    let sig = key.sign_prehashed::<H>(&digest).unwrap();
    let openssl_sig = EcdsaSig::from_private_components(
        BigNum::from_slice(&sig[..32]).unwrap(),
        BigNum::from_slice(&sig[32..]).unwrap(),
    )
    .unwrap();
    let mut g = c.benchmark_group(format!("ecdsa_secp256k1_{name}_verify_prehashed"));
    g.bench_function(BenchmarkId::new(VG, H::OUTPUT_SIZE), |b| {
        b.iter(|| {
            verifying_key
                .verify_prehashed::<H>(black_box(&digest), &sig)
                .unwrap()
        })
    });
    g.bench_function(BenchmarkId::new(OPENSSL, H::OUTPUT_SIZE), |b| {
        b.iter(|| {
            let point = EcPoint::from_bytes(&group, black_box(&q), &mut ctx).unwrap();
            let ec = EcKey::from_public_key(&group, &point).unwrap();
            ec.check_key().unwrap();
            assert!(openssl_sig.verify(black_box(digest.as_ref()), &ec).unwrap());
        })
    });
    g.finish();

    let mut g = c.benchmark_group(format!("ecdsa_secp256k1_{name}_verify"));
    for size in SIZES {
        let message = vec![0x5a; size];
        let sig = key.sign::<H>(&message).unwrap();
        let der = EcdsaSig::from_private_components(
            BigNum::from_slice(&sig[..32]).unwrap(),
            BigNum::from_slice(&sig[32..]).unwrap(),
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
    }
    g.finish();
}

#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_: &mut Criterion) {}
