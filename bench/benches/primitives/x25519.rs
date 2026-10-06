//! X25519.

use criterion::Criterion;

pub const USES: &[&str] = &["x25519"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use aws_lc_rs::agreement::{self, UnparsedPublicKey};
    use aws_lc_rs::encoding::{AsBigEndian, Curve25519SeedBin};
    use aws_lc_rs::error::Unspecified;
    use criterion::BenchmarkId;
    use openssl::derive::Deriver;
    use openssl::pkey::{Id, PKey};
    use verified_garbage::x25519::{PrivateKey, x25519};

    use crate::{AWS_LC, OPENSSL, VG};
    let private = [0x42; 32];
    let peer = PrivateKey::from_bytes(&[0x24; 32]).public_key();
    // Each side's private key is loaded once, outside the measurements, as a
    // party holds its key across exchanges (OpenSSL's and aws-lc-rs's imports
    // also derive the public key, a second scalar multiplication); the peer's
    // public key comes with each exchange.
    let vg_private = PrivateKey::from_bytes(&private);
    let openssl_private = PKey::private_key_from_raw_bytes(&private, Id::X25519).unwrap();
    let aws_lc_private =
        agreement::PrivateKey::from_private_key(&agreement::X25519, &private).unwrap();
    // aws-lc-rs's Diffie-Hellman (which also rejects an all-zero secret),
    // decoding the peer's public key as OpenSSL's does.
    let aws_lc_agree = |private: &agreement::PrivateKey, peer: &[u8; 32]| {
        agreement::agree(
            private,
            UnparsedPublicKey::new(&agreement::X25519, peer),
            Unspecified,
            |s| Ok(s.to_vec()),
        )
        .unwrap()
    };
    assert_eq!(
        aws_lc_agree(&aws_lc_private, &peer),
        vg_private.diffie_hellman(&peer).unwrap()
    );
    assert_eq!(
        aws_lc_private.compute_public_key().unwrap().as_ref(),
        vg_private.public_key()
    );
    let mut g = c.benchmark_group("x25519");
    // One Diffie-Hellman: a shared secret from a private key and the peer's
    // public key. The ids' size is the bytes of the shared secret.
    g.bench_function(BenchmarkId::new(VG, 32), |b| {
        b.iter(|| {
            black_box(&vg_private)
                .diffie_hellman(black_box(&peer))
                .unwrap()
        })
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 32), |b| {
        b.iter(|| {
            let peer = PKey::public_key_from_raw_bytes(black_box(&peer), Id::X25519).unwrap();
            let mut d = Deriver::new(black_box(&openssl_private)).unwrap();
            d.set_peer(&peer).unwrap();
            d.derive_to_vec().unwrap()
        })
    });
    g.bench_function(BenchmarkId::new(AWS_LC, 32), |b| {
        b.iter(|| aws_lc_agree(black_box(&aws_lc_private), black_box(&peer)))
    });
    g.finish();

    // Neither OpenSSL nor aws-lc-rs has a function of the scalar
    // multiplication alone: their nearest is the same Diffie-Hellman (which
    // also rejects an all-zero secret).
    let mut g = c.benchmark_group("x25519_raw");
    g.bench_function(BenchmarkId::new(VG, 32), |b| {
        b.iter(|| x25519(black_box(&private), black_box(&peer)))
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 32), |b| {
        b.iter(|| {
            let peer = PKey::public_key_from_raw_bytes(black_box(&peer), Id::X25519).unwrap();
            let mut d = Deriver::new(black_box(&openssl_private)).unwrap();
            d.set_peer(&peer).unwrap();
            d.derive_to_vec().unwrap()
        })
    });
    g.bench_function(BenchmarkId::new(AWS_LC, 32), |b| {
        b.iter(|| aws_lc_agree(black_box(&aws_lc_private), black_box(&peer)))
    });
    g.finish();

    let mut g = c.benchmark_group("x25519_public_key");
    g.bench_function(BenchmarkId::new(VG, 32), |b| {
        b.iter(|| PrivateKey::from_bytes(black_box(&private)).public_key())
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 32), |b| {
        b.iter(|| {
            PKey::private_key_from_raw_bytes(black_box(&private), Id::X25519)
                .unwrap()
                .raw_public_key()
                .unwrap()
        })
    });
    g.bench_function(BenchmarkId::new(AWS_LC, 32), |b| {
        b.iter(|| {
            agreement::PrivateKey::from_private_key(&agreement::X25519, black_box(&private))
                .unwrap()
                .compute_public_key()
                .unwrap()
        })
    });
    g.finish();

    // A new key pair: a random private key and its public key, which
    // OpenSSL's and aws-lc-rs's key generation always derive.
    let mut g = c.benchmark_group("x25519_generate");
    g.bench_function(BenchmarkId::new(VG, 32), |b| {
        b.iter(|| {
            let key = PrivateKey::generate().unwrap();
            (*key.as_bytes(), key.public_key())
        })
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 32), |b| {
        b.iter(|| {
            let key = PKey::generate_x25519().unwrap();
            (
                key.raw_private_key().unwrap(),
                key.raw_public_key().unwrap(),
            )
        })
    });
    g.bench_function(BenchmarkId::new(AWS_LC, 32), |b| {
        b.iter(|| {
            let key = agreement::PrivateKey::generate(&agreement::X25519).unwrap();
            let private: Curve25519SeedBin = key.as_be_bytes().unwrap();
            (private, key.compute_public_key().unwrap())
        })
    });
    g.finish();
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64"
)))]
pub fn bench(_: &mut Criterion) {}
