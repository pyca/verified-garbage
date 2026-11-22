//! HKDF (RFC 5869) with SHA-256 and SHA-384, as TLS 1.3 uses it.

use criterion::Criterion;

pub const USES: &[&str] = &["hkdf", "hmac_sha256", "hmac_sha384", "sha256", "sha384"];

#[cfg(any(target_arch = "riscv64", target_arch = "x86_64"))]
pub fn bench(c: &mut Criterion) {
    use openssl::md::Md;
    use verified_garbage::hashes::sha256::Sha256;
    use verified_garbage::hashes::sha384::Sha384;

    group::<Sha256>(c, "hkdf-sha256", Md::sha256(), aws_lc_rs::hkdf::HKDF_SHA256);
    group::<Sha384>(c, "hkdf-sha384", Md::sha384(), aws_lc_rs::hkdf::HKDF_SHA384);
}

/// HKDF over `H` against OpenSSL's over `md` and aws-lc-rs's `alg`:
/// HKDF-Extract of a 32-byte secret with a salt of a digest (TLS 1.3's
/// key schedule's), into a pseudorandom key ready to expand; and
/// HKDF-Expand from it, with a 20-byte context (a TLS 1.3 `HkdfLabel`'s
/// size), of a digest (a secret), 64 bytes and 1024 bytes.
///
/// Each library's pseudorandom key is made once, outside the expansion's
/// measurements, as TLS 1.3 derives several keys from each secret: it is
/// verified-garbage's `Hkdf`, which holds HMAC keyed with it, aws-lc-rs's
/// `Prk` and, for OpenSSL, whose HKDF takes the key with each derivation, its
/// bytes (`EXPAND_ONLY`).
#[cfg(any(target_arch = "riscv64", target_arch = "x86_64"))]
fn group<H: verified_garbage::kdf::hkdf::HkdfHash>(
    c: &mut Criterion,
    name: &str,
    md: &'static openssl::md::MdRef,
    alg: aws_lc_rs::hkdf::Algorithm,
) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::pkey::Id;
    use openssl::pkey_ctx::{HkdfMode, PkeyCtx};
    use verified_garbage::kdf::hkdf::Hkdf;

    use crate::{AWS_LC, BenchDyn, OPENSSL, VG};

    /// aws-lc-rs's output length, as its `expand` takes it.
    struct Len(usize);
    impl aws_lc_rs::hkdf::KeyType for Len {
        fn len(&self) -> usize {
            self.0
        }
    }

    let d = H::OUTPUT_SIZE;
    let ikm = [0x0b; 32];
    let salt = vec![0x5a; d];
    let info = [0x42; 20];

    // OpenSSL's HKDF-Extract (`extract`, with `salt`) or HKDF-Expand (with
    // `info`), with the key `key` (the secret, or the pseudorandom key),
    // into `out`.
    let openssl_hkdf = |extract: bool, key: &[u8], salt: &[u8], info: &[u8], out: &mut [u8]| {
        let mut ctx = PkeyCtx::new_id(Id::HKDF).unwrap();
        ctx.derive_init().unwrap();
        ctx.set_hkdf_md(md).unwrap();
        ctx.set_hkdf_key(key).unwrap();
        if extract {
            ctx.set_hkdf_mode(HkdfMode::EXTRACT_ONLY).unwrap();
            ctx.set_hkdf_salt(salt).unwrap();
        } else {
            ctx.set_hkdf_mode(HkdfMode::EXPAND_ONLY).unwrap();
            ctx.add_hkdf_info(info).unwrap();
        }
        ctx.derive(Some(out)).unwrap();
    };

    let (prk, vg) = Hkdf::<H>::extract(Some(&salt), &ikm);
    let mut openssl_prk = vec![0; d];
    openssl_hkdf(true, &ikm, &salt, &[], &mut openssl_prk);
    assert_eq!(openssl_prk, prk.as_ref());
    let aws_lc = aws_lc_rs::hkdf::Salt::new(alg, &salt).extract(&ikm);

    let mut g = c.benchmark_group(format!("{name}-extract"));
    g.bench(BenchmarkId::new(VG, d), |b| {
        b.iter(|| Hkdf::<H>::new(Some(black_box(&salt)), black_box(&ikm)))
    });
    g.bench(BenchmarkId::new(OPENSSL, d), |b| {
        let mut out = vec![0; d];
        b.iter(|| openssl_hkdf(true, black_box(&ikm), black_box(&salt), &[], &mut out))
    });
    g.bench(BenchmarkId::new(AWS_LC, d), |b| {
        b.iter(|| aws_lc_rs::hkdf::Salt::new(alg, black_box(&salt)).extract(black_box(&ikm)))
    });
    g.finish();

    let mut g = c.benchmark_group(format!("{name}-expand"));
    for size in [d, 64, 1024] {
        g.throughput(Throughput::Bytes(size as u64));
        let mut expected = vec![0; size];
        vg.expand(&info, &mut expected).unwrap();
        let mut out = vec![0; size];
        openssl_hkdf(false, &openssl_prk, &[], &info, &mut out);
        assert_eq!(out, expected);
        aws_lc
            .expand(&[&info], Len(size))
            .unwrap()
            .fill(&mut out)
            .unwrap();
        assert_eq!(out, expected);
        g.bench(BenchmarkId::new(VG, size), |b| {
            b.iter(|| black_box(&vg).expand(black_box(&info), &mut out).unwrap())
        });
        g.bench(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                openssl_hkdf(
                    false,
                    black_box(&openssl_prk),
                    &[],
                    black_box(&info),
                    &mut out,
                )
            })
        });
        g.bench(BenchmarkId::new(AWS_LC, size), |b| {
            b.iter(|| {
                black_box(&aws_lc)
                    .expand(&[black_box(&info)], Len(size))
                    .unwrap()
                    .fill(&mut out)
                    .unwrap()
            })
        });
    }
    g.finish();
}

#[cfg(not(any(target_arch = "riscv64", target_arch = "x86_64")))]
pub fn bench(_: &mut Criterion) {}
