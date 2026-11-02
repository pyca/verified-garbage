//! ECDH over p192 beside OpenSSL (aws-lc-rs has no ECDH over p192).

use criterion::Criterion;

pub const USES: &[&str] = &["ecdh_p192", "ec_p192", "ec_p192_validate"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64",
    all(target_arch = "powerpc64", target_endian = "little")
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use openssl::bn::{BigNum, BigNumContext};
    use openssl::derive::Deriver;
    use openssl::ec::{EcGroup, EcKey, EcPoint};
    use openssl::nid::Nid;
    use openssl::pkey::PKey;
    use verified_garbage::ecdh::{P192, PrivateKey};

    use crate::{BenchDyn, OPENSSL, VG};

    // Keys below p192's order.
    let d = [0x42; 24];
    let peer_d = [0x24; 24];
    let peer = PrivateKey::<P192>::from_bytes(&peer_d)
        .public_key()
        .unwrap();
    let group = EcGroup::from_curve_name(Nid::X9_62_PRIME192V1).unwrap();
    let mut ctx = BigNumContext::new().unwrap();
    let d_bn = BigNum::from_slice(&d).unwrap();
    let mut public = EcPoint::new(&group).unwrap();
    public.mul_generator2(&group, &d_bn, &mut ctx).unwrap();
    // Each side's private key is loaded once, outside the measurements, as a
    // party holds its key across exchanges; the peer's public key comes with
    // each exchange, and is decoded and validated in it.
    let vg_private = PrivateKey::<P192>::from_bytes(&d);
    let openssl_private =
        PKey::from_ec_key(EcKey::from_private_components(&group, &d_bn, &public).unwrap()).unwrap();
    let mut g = c.benchmark_group("ecdh_p192");
    // The ids' size is the bytes of the shared secret.
    g.bench(BenchmarkId::new(VG, 24), |b| {
        b.iter(|| {
            black_box(&vg_private)
                .diffie_hellman(black_box(&peer))
                .unwrap()
        })
    });
    g.bench(BenchmarkId::new(OPENSSL, 24), |b| {
        b.iter(|| {
            let point = EcPoint::from_bytes(&group, black_box(&peer), &mut ctx).unwrap();
            let peer = PKey::from_ec_key(EcKey::from_public_key(&group, &point).unwrap()).unwrap();
            let mut d = Deriver::new(black_box(&openssl_private)).unwrap();
            d.set_peer(&peer).unwrap();
            d.derive_to_vec().unwrap()
        })
    });
    g.finish();

    #[cfg(target_arch = "x86_64")]
    {
        let mut g = c.benchmark_group("ec_validate_p192");
        g.bench(BenchmarkId::new(VG, 49), |b| {
            b.iter(|| P192::validate_public_key(black_box(&peer)))
        });
        g.bench(BenchmarkId::new(OPENSSL, 49), |b| {
            b.iter(|| {
                let point = EcPoint::from_bytes(&group, black_box(&peer), &mut ctx).unwrap();
                // OpenSSL validates coordinates and the curve equation while decoding.
                !point.is_infinity(&group)
            })
        });
        // aws-lc-rs has no standalone public-point validation API.
        let mut one = [0; 24];
        one[23] = 1;
        let key = PrivateKey::<P192>::from_bytes(&one);
        g.bench(BenchmarkId::new("scalar-multiply", 49), |b| {
            b.iter(|| black_box(&key).diffie_hellman(black_box(&peer)).is_ok())
        });
        g.finish();
    }
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64",
    all(target_arch = "powerpc64", target_endian = "little")
)))]
pub fn bench(_: &mut Criterion) {}
