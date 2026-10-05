//! RSASSA-PSS with MGF1 of a SHA-256 hash value, with a 32-byte salt:
//! signing and verifying, beside OpenSSL.

use criterion::Criterion;

pub const USES: &[&str] = &["rsa_pss_sha256_mgf1_sha256", "rsa"];

/// Moduli of 2048, 3072 and 4096 bits with the exponent 65537; the ids'
/// size is the modulus' bytes. Each library loads the key once, outside the
/// measurements, and is given the hash value (OpenSSL through `EVP_PKEY_sign`
/// and `EVP_PKEY_verify` with PSS padding, SHA-256 as the hash and MGF1's
/// hash, and a salt as long as the hash value, with its default blinding
/// when signing).
#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use openssl::md::Md;
    use openssl::pkey::PKey;
    use openssl::pkey_ctx::PkeyCtx;
    use openssl::rsa::{Padding, Rsa};
    use openssl::sign::RsaPssSaltlen;
    use verified_garbage::rsa::{PrivateKey, PublicKey};
    use verified_garbage::rsa_pss::{Hash, SaltLength, sign, verify};

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
            let sig = sign(&vg_private, &digest, Hash::Sha256, Hash::Sha256, 32).unwrap();
            (PKey::from_rsa(key).unwrap(), vg_private, vg_public, sig)
        })
        .collect();
    let ctx = |pkey: &PKey<openssl::pkey::Private>, init: fn(&mut PkeyCtx<_>)| {
        let mut ctx = PkeyCtx::new(pkey).unwrap();
        init(&mut ctx);
        ctx.set_rsa_padding(Padding::PKCS1_PSS).unwrap();
        ctx.set_signature_md(Md::sha256()).unwrap();
        ctx.set_rsa_mgf1_md(Md::sha256()).unwrap();
        ctx.set_rsa_pss_saltlen(RsaPssSaltlen::DIGEST_LENGTH).unwrap();
        ctx
    };

    let mut g = c.benchmark_group("rsa_pss_sign");
    for (pkey, vg_private, _, sig) in &keys {
        let k = sig.len();
        g.bench_function(BenchmarkId::new(VG, k), |b| {
            b.iter(|| {
                sign(
                    black_box(vg_private),
                    black_box(&digest),
                    Hash::Sha256,
                    Hash::Sha256,
                    32,
                )
                .unwrap()
            })
        });
        let mut c = ctx(pkey, |c| c.sign_init().unwrap());
        let mut out = vec![0; k];
        g.bench_function(BenchmarkId::new(OPENSSL, k), |b| {
            b.iter(|| c.sign(black_box(&digest), Some(&mut out)).unwrap())
        });
    }
    g.finish();

    let mut g = c.benchmark_group("rsa_pss_verify");
    for (pkey, _, vg_public, sig) in &keys {
        let k = sig.len();
        g.bench_function(BenchmarkId::new(VG, k), |b| {
            b.iter(|| {
                assert!(verify(
                    black_box(vg_public),
                    black_box(sig),
                    &digest,
                    Hash::Sha256,
                    Hash::Sha256,
                    SaltLength::Len(32)
                ))
            })
        });
        let mut c = ctx(pkey, |c| c.verify_init().unwrap());
        g.bench_function(BenchmarkId::new(OPENSSL, k), |b| {
            b.iter(|| assert!(c.verify(black_box(&digest), black_box(sig)).unwrap()))
        });
    }
    g.finish();
}

#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_: &mut Criterion) {}
