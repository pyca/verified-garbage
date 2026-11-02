//! Validated SEC 1 conversion beside OpenSSL, for each curve (the
//! `ec_compressed_<curve>.rs` benchmarks). aws-lc-rs has no standalone
//! validated point-conversion API.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

/// Runs, in `$c`, the compression and decompression benchmarks of the curve
/// `verified_garbage::ecdh::$curve`, in groups named `ec_<$name>_compress`
/// and `ec_<$name>_decompress`, from the key `7G`.
macro_rules! ec_compressed_bench {
    ($c:expr, verified_garbage::ecdh::$curve:ident, $name:literal, $len:literal, $nid:ident) => {{
        use std::hint::black_box;

        use criterion::BenchmarkId;
        use openssl::bn::{BigNum, BigNumContext};
        use openssl::ec::{EcGroup, EcPoint, PointConversionForm};
        use openssl::nid::Nid;
        use verified_garbage::ecdh::$curve;

        use crate::{BenchDyn, OPENSSL, VG};

        let c: &mut criterion::Criterion = $c;
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
        g.bench(BenchmarkId::new(VG, $len + 1), |b| {
            b.iter(|| $curve::compress_public_key(black_box(&public)).unwrap())
        });
        g.bench(BenchmarkId::new(OPENSSL, $len + 1), |b| {
            b.iter(|| {
                let q = EcPoint::from_bytes(&group, black_box(&public), &mut ctx).unwrap();
                assert!(q.is_on_curve(&group, &mut ctx).unwrap());
                q.to_bytes(&group, PointConversionForm::COMPRESSED, &mut ctx)
                    .unwrap()
            })
        });
        g.finish();
        let mut g = c.benchmark_group(concat!("ec_", $name, "_decompress"));
        g.bench(BenchmarkId::new(VG, 2 * $len + 1), |b| {
            b.iter(|| $curve::decompress_public_key(black_box(&compressed)).unwrap())
        });
        g.bench(BenchmarkId::new(OPENSSL, 2 * $len + 1), |b| {
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

pub(crate) use ec_compressed_bench;
