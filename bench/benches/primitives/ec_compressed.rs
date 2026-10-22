//! Validated SEC 1 conversion beside OpenSSL. aws-lc-rs has no standalone
//! validated point-conversion API.

use criterion::Criterion;

pub const USES: &[&str] = &[
    "ec_p192_compressed",
    "ec_p224_compressed",
    "ec_p256_compressed",
    "ec_p384_compressed",
    "ec_p521_compressed",
    "ec_secp256k1_compressed",
    "ec_brainpoolp256r1_compressed",
    "ec_brainpoolp384r1_compressed",
    "ec_brainpoolp512r1_compressed",
];

#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use crate::{OPENSSL, VG};
    use criterion::BenchmarkId;
    use openssl::bn::{BigNum, BigNumContext};
    use openssl::ec::{EcGroup, EcPoint, PointConversionForm};
    use openssl::nid::Nid;
    use std::hint::black_box;

    macro_rules! curve {
        ($curve:ident, $name:literal, $len:literal, $nid:ident) => {{
            use verified_garbage::ecdh::$curve;
            let group = EcGroup::from_curve_name(Nid::$nid).unwrap();
            let mut ctx = BigNumContext::new().unwrap();
            let scalar = BigNum::from_u32(7).unwrap();
            let mut point = EcPoint::new(&group).unwrap();
            point.mul_generator2(&group, &scalar, &mut ctx).unwrap();
            let public: [u8; 2 * $len + 1] = point
                .to_bytes(&group, PointConversionForm::UNCOMPRESSED, &mut ctx)
                .unwrap()
                .try_into()
                .unwrap();
            let compressed = $curve::compress_public_key(&public).unwrap();
            assert_eq!($curve::decompress_public_key(&compressed), Some(public));
            let mut g = c.benchmark_group(concat!("ec_", $name, "_compress"));
            g.bench_function(BenchmarkId::new(VG, $len + 1), |b| {
                b.iter(|| $curve::compress_public_key(black_box(&public)).unwrap())
            });
            g.bench_function(BenchmarkId::new(OPENSSL, $len + 1), |b| {
                b.iter(|| {
                    let q = EcPoint::from_bytes(&group, black_box(&public), &mut ctx).unwrap();
                    assert!(q.is_on_curve(&group, &mut ctx).unwrap());
                    q.to_bytes(&group, PointConversionForm::COMPRESSED, &mut ctx)
                        .unwrap()
                })
            });
            g.finish();
            let mut g = c.benchmark_group(concat!("ec_", $name, "_decompress"));
            g.bench_function(BenchmarkId::new(VG, 2 * $len + 1), |b| {
                b.iter(|| $curve::decompress_public_key(black_box(&compressed)).unwrap())
            });
            g.bench_function(BenchmarkId::new(OPENSSL, 2 * $len + 1), |b| {
                b.iter(|| {
                    let q = EcPoint::from_bytes(&group, black_box(&compressed), &mut ctx).unwrap();
                    assert!(q.is_on_curve(&group, &mut ctx).unwrap());
                    q.to_bytes(&group, PointConversionForm::UNCOMPRESSED, &mut ctx)
                        .unwrap()
                })
            });
            g.finish();
        }};
    }
    curve!(P192, "p192", 24, X9_62_PRIME192V1);
    curve!(P224, "p224", 28, SECP224R1);
    curve!(P256, "p256", 32, X9_62_PRIME256V1);
    curve!(P384, "p384", 48, SECP384R1);
    curve!(P521, "p521", 66, SECP521R1);
    curve!(Secp256k1, "secp256k1", 32, SECP256K1);
    curve!(BrainpoolP256r1, "brainpoolp256r1", 32, BRAINPOOL_P256R1);
    curve!(BrainpoolP384r1, "brainpoolp384r1", 48, BRAINPOOL_P384R1);
    curve!(BrainpoolP512r1, "brainpoolp512r1", 64, BRAINPOOL_P512R1);
}

#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_: &mut Criterion) {}
