//! ECDH over P-384 beside OpenSSL and aws-lc-rs.

use criterion::Criterion;

pub const USES: &[&str] = &["ecdh_p384", "ec_p384", "ec_p384_validate"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
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
    use verified_garbage::ecdh::{P384, PrivateKey};

    use crate::{AWS_LC, BenchDyn, OPENSSL, VG};

    let d = [0x42; 48];
    let peer = PrivateKey::<P384>::from_bytes(&[0x24; 48])
        .public_key()
        .unwrap();
    let group = EcGroup::from_curve_name(Nid::SECP384R1).unwrap();
    let mut ctx = BigNumContext::new().unwrap();
    let d_bn = BigNum::from_slice(&d).unwrap();
    let mut public = EcPoint::new(&group).unwrap();
    public.mul_generator2(&group, &d_bn, &mut ctx).unwrap();
    // Each side's private key is loaded once, outside the measurements, as a
    // party holds its key across exchanges; the peer's public key comes with
    // each exchange, and is decoded and validated in it.
    let vg_private = PrivateKey::<P384>::from_bytes(&d);
    let openssl_private =
        PKey::from_ec_key(EcKey::from_private_components(&group, &d_bn, &public).unwrap()).unwrap();
    let aws_lc_private =
        agreement::PrivateKey::from_private_key(&agreement::ECDH_P384, &d).unwrap();
    // aws-lc-rs decodes and validates the peer's public key in `agree`.
    let aws_lc_agree = |private: &agreement::PrivateKey, peer: &[u8]| {
        agreement::agree(
            private,
            UnparsedPublicKey::new(&agreement::ECDH_P384, peer),
            Unspecified,
            |s| Ok(s.to_vec()),
        )
        .unwrap()
    };
    assert_eq!(
        aws_lc_agree(&aws_lc_private, &peer),
        vg_private.diffie_hellman(&peer).unwrap()
    );
    let mut g = c.benchmark_group("ecdh_p384");
    // The ids' size is the bytes of the shared secret.
    g.bench(BenchmarkId::new(VG, 48), |b| {
        b.iter(|| {
            black_box(&vg_private)
                .diffie_hellman(black_box(&peer))
                .unwrap()
        })
    });
    g.bench(BenchmarkId::new(OPENSSL, 48), |b| {
        b.iter(|| {
            let point = EcPoint::from_bytes(&group, black_box(&peer), &mut ctx).unwrap();
            let peer = PKey::from_ec_key(EcKey::from_public_key(&group, &point).unwrap()).unwrap();
            let mut d = Deriver::new(black_box(&openssl_private)).unwrap();
            d.set_peer(&peer).unwrap();
            d.derive_to_vec().unwrap()
        })
    });
    g.bench(BenchmarkId::new(AWS_LC, 48), |b| {
        b.iter(|| aws_lc_agree(black_box(&aws_lc_private), black_box(&peer)))
    });
    g.finish();

    #[cfg(target_arch = "x86_64")]
    {
        let mut g = c.benchmark_group("ec_validate_p384");
        g.bench(BenchmarkId::new(VG, 97), |b| {
            b.iter(|| P384::validate_public_key(black_box(&peer)))
        });
        g.bench(BenchmarkId::new(OPENSSL, 97), |b| {
            b.iter(|| {
                let point = EcPoint::from_bytes(&group, black_box(&peer), &mut ctx).unwrap();
                // OpenSSL validates coordinates and the curve equation while decoding.
                !point.is_infinity(&group)
            })
        });
        // aws-lc-rs has no standalone public-point validation API.
        let mut one = [0; 48];
        one[47] = 1;
        let key = PrivateKey::<P384>::from_bytes(&one);
        g.bench(BenchmarkId::new("scalar-multiply", 97), |b| {
            b.iter(|| black_box(&key).diffie_hellman(black_box(&peer)).is_ok())
        });
        g.finish();
    }
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
)))]
pub fn bench(_: &mut Criterion) {}
