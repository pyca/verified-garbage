//! ECDH over P-521 beside OpenSSL and aws-lc-rs.

use criterion::Criterion;

pub const USES: &[&str] = &["ecdh_p521", "ec_p521"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use aws_lc_rs::agreement::{self, UnparsedPublicKey};
    use aws_lc_rs::error::Unspecified;
    use criterion::BenchmarkId;
    use openssl::bn::{BigNum, BigNumContext};
    use openssl::derive::Deriver;
    use openssl::ec::{EcGroup, EcKey, EcPoint};
    use openssl::nid::Nid;
    use openssl::pkey::PKey;
    use verified_garbage::ecdh::{P521, PrivateKey};

    use crate::{AWS_LC, OPENSSL, VG};

    // Keys below P-521's order, whose top byte is at most 1.
    let mut d = [0x42; 66];
    d[0] = 1;
    let mut peer_d = [0x24; 66];
    peer_d[0] = 1;
    let peer = PrivateKey::<P521>::from_bytes(&peer_d)
        .public_key()
        .unwrap();
    let group = EcGroup::from_curve_name(Nid::SECP521R1).unwrap();
    let mut ctx = BigNumContext::new().unwrap();
    let d_bn = BigNum::from_slice(&d).unwrap();
    let mut public = EcPoint::new(&group).unwrap();
    public.mul_generator2(&group, &d_bn, &mut ctx).unwrap();
    // Each side's private key is loaded once, outside the measurements, as a
    // party holds its key across exchanges; the peer's public key comes with
    // each exchange, and is decoded and validated in it.
    let vg_private = PrivateKey::<P521>::from_bytes(&d);
    let openssl_private =
        PKey::from_ec_key(EcKey::from_private_components(&group, &d_bn, &public).unwrap()).unwrap();
    let aws_lc_private =
        agreement::PrivateKey::from_private_key(&agreement::ECDH_P521, &d).unwrap();
    // aws-lc-rs decodes and validates the peer's public key in `agree`.
    let aws_lc_agree = |private: &agreement::PrivateKey, peer: &[u8]| {
        agreement::agree(
            private,
            UnparsedPublicKey::new(&agreement::ECDH_P521, peer),
            Unspecified,
            |s| Ok(s.to_vec()),
        )
        .unwrap()
    };
    assert_eq!(
        aws_lc_agree(&aws_lc_private, &peer),
        vg_private.diffie_hellman(&peer).unwrap()
    );
    let mut g = c.benchmark_group("ecdh_p521");
    // The ids' size is the bytes of the shared secret.
    g.bench_function(BenchmarkId::new(VG, 66), |b| {
        b.iter(|| {
            black_box(&vg_private)
                .diffie_hellman(black_box(&peer))
                .unwrap()
        })
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 66), |b| {
        b.iter(|| {
            let point = EcPoint::from_bytes(&group, black_box(&peer), &mut ctx).unwrap();
            let peer = PKey::from_ec_key(EcKey::from_public_key(&group, &point).unwrap()).unwrap();
            let mut d = Deriver::new(black_box(&openssl_private)).unwrap();
            d.set_peer(&peer).unwrap();
            d.derive_to_vec().unwrap()
        })
    });
    g.bench_function(BenchmarkId::new(AWS_LC, 66), |b| {
        b.iter(|| aws_lc_agree(black_box(&aws_lc_private), black_box(&peer)))
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
