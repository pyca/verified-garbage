//! RSASSA-PKCS1-v1_5 of a SHA-256 hash value: signing, verifying and
//! recovering the hash value, beside OpenSSL.

use criterion::Criterion;

pub const USES: &[&str] = &["rsa_pkcs1_sig", "rsa"];

/// Moduli of 2048, 3072 and 4096 bits with the exponent 65537; the ids'
/// size is the modulus' bytes. Each library loads the key once, outside the
/// measurements, and is given the hash value (OpenSSL through `EVP_PKEY_sign`,
/// `EVP_PKEY_verify` and `EVP_PKEY_verify_recover` with PKCS #1 v1.5 padding
/// and SHA-256 set, with its default blinding when signing).
#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use openssl::md::Md;
    use openssl::pkey::PKey;
    use openssl::pkey_ctx::PkeyCtx;
    use openssl::rsa::{Padding, Rsa};
    use verified_garbage::rsa::{PrivateKey, PublicKey};
    use verified_garbage::rsa_pkcs1_sig::{Hash, recover, sign, verify};

    use crate::{OPENSSL, VG};

    let digest = [0x42; 32];
    let keys: Vec<_> = [2048, 3072, 4096]
        .into_iter()
        .map(|bits| {
            let key = Rsa::generate(bits).unwrap();
            let vg_private = PrivateKey::from_crt(
                &key.n().to_vec(),
                &key.e().to_vec(),
                &key.d().to_vec(),
                &key.p().unwrap().to_vec(),
                &key.q().unwrap().to_vec(),
                &key.dmp1().unwrap().to_vec(),
                &key.dmq1().unwrap().to_vec(),
                &key.iqmp().unwrap().to_vec(),
            )
            .unwrap();
            let vg_public = PublicKey::new(&key.n().to_vec(), &key.e().to_vec()).unwrap();
            let sig = sign(&vg_private, &digest, Hash::Sha256).unwrap();
            (PKey::from_rsa(key).unwrap(), vg_private, vg_public, sig)
        })
        .collect();
    let ctx = |pkey: &PKey<openssl::pkey::Private>, init: fn(&mut PkeyCtx<_>)| {
        let mut ctx = PkeyCtx::new(pkey).unwrap();
        init(&mut ctx);
        ctx.set_rsa_padding(Padding::PKCS1).unwrap();
        ctx.set_signature_md(Md::sha256()).unwrap();
        ctx
    };

    let mut g = c.benchmark_group("rsa_pkcs1_sign");
    for (pkey, vg_private, _, sig) in &keys {
        let k = sig.len();
        g.bench_function(BenchmarkId::new(VG, k), |b| {
            b.iter(|| sign(black_box(vg_private), black_box(&digest), Hash::Sha256).unwrap())
        });
        let mut c = ctx(pkey, |c| c.sign_init().unwrap());
        let mut out = vec![0; k];
        g.bench_function(BenchmarkId::new(OPENSSL, k), |b| {
            b.iter(|| c.sign(black_box(&digest), Some(&mut out)).unwrap())
        });
    }
    g.finish();

    let mut g = c.benchmark_group("rsa_pkcs1_verify");
    for (pkey, _, vg_public, sig) in &keys {
        let k = sig.len();
        g.bench_function(BenchmarkId::new(VG, k), |b| {
            b.iter(|| {
                assert!(verify(
                    black_box(vg_public),
                    black_box(sig),
                    &digest,
                    Hash::Sha256
                ))
            })
        });
        let mut c = ctx(pkey, |c| c.verify_init().unwrap());
        g.bench_function(BenchmarkId::new(OPENSSL, k), |b| {
            b.iter(|| assert!(c.verify(black_box(&digest), black_box(sig)).unwrap()))
        });
    }
    g.finish();

    let mut g = c.benchmark_group("rsa_pkcs1_recover");
    for (pkey, _, vg_public, sig) in &keys {
        let k = sig.len();
        g.bench_function(BenchmarkId::new(VG, k), |b| {
            b.iter(|| recover(black_box(vg_public), black_box(sig), Hash::Sha256).unwrap())
        });
        let mut c = ctx(pkey, |c| c.verify_recover_init().unwrap());
        let mut out = vec![0; k];
        g.bench_function(BenchmarkId::new(OPENSSL, k), |b| {
            b.iter(|| c.verify_recover(black_box(sig), Some(&mut out)).unwrap())
        });
    }
    g.finish();
}

#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_: &mut Criterion) {}
