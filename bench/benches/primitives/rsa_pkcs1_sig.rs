//! RSASSA-PKCS1-v1_5 of a SHA-256 hash value: signing, verifying and
//! recovering the hash value, beside OpenSSL and (signing and verifying)
//! aws-lc-rs.

use criterion::Criterion;

pub const USES: &[&str] = &["rsa_pkcs1_sig", "rsa"];

/// Moduli of 2048, 3072 and 4096 bits with the exponent 65537; the ids'
/// size is the modulus' bytes. Each library loads the key once, outside the
/// measurements, and is given the hash value (OpenSSL through `EVP_PKEY_sign`,
/// `EVP_PKEY_verify` and `EVP_PKEY_verify_recover` with PKCS #1 v1.5 padding
/// and SHA-256 set, with its default blinding when signing; aws-lc-rs
/// through `KeyPair::sign_digest` and `ParsedPublicKey::verify_digest_sig`,
/// which set up an `EVP_PKEY_CTX` in every operation, from a key loaded from
/// its components). aws-lc-rs has no recovery of the hash value.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use aws_lc_rs::digest::{Digest, SHA256};
    use aws_lc_rs::rsa::KeyPairComponents;
    use aws_lc_rs::signature::{
        RSA_PKCS1_2048_8192_SHA256, RSA_PKCS1_SHA256, RsaKeyPair, RsaPublicKeyComponents,
    };
    use criterion::BenchmarkId;
    use openssl::md::Md;
    use openssl::pkey::PKey;
    use openssl::pkey_ctx::PkeyCtx;
    use openssl::rsa::{Padding, Rsa};
    use verified_garbage::rsa::{PrivateKey, PublicKey};
    use verified_garbage::rsa_pkcs1_sig::{Hash, recover, sign, verify};

    use crate::{AWS_LC, OPENSSL, VG};

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
            let (n, e) = (key.n().to_vec(), key.e().to_vec());
            let aws_private = RsaKeyPair::from_components(&KeyPairComponents {
                public_key: RsaPublicKeyComponents { n: &n, e: &e },
                d: key.d().to_vec(),
                p: key.p().unwrap().to_vec(),
                q: key.q().unwrap().to_vec(),
                dP: key.dmp1().unwrap().to_vec(),
                dQ: key.dmq1().unwrap().to_vec(),
                qInv: key.iqmp().unwrap().to_vec(),
            })
            .unwrap();
            let aws_public = RsaPublicKeyComponents { n: &n, e: &e }
                .to_parsed_public_key(&RSA_PKCS1_2048_8192_SHA256)
                .unwrap();
            (
                PKey::from_rsa(key).unwrap(),
                vg_private,
                vg_public,
                sig,
                aws_private,
                aws_public,
            )
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
    for (pkey, vg_private, _, sig, aws_private, _) in &keys {
        let k = sig.len();
        g.bench_function(BenchmarkId::new(VG, k), |b| {
            b.iter(|| sign(black_box(vg_private), black_box(&digest), Hash::Sha256).unwrap())
        });
        let mut c = ctx(pkey, |c| c.sign_init().unwrap());
        let mut out = vec![0; k];
        g.bench_function(BenchmarkId::new(OPENSSL, k), |b| {
            b.iter(|| c.sign(black_box(&digest), Some(&mut out)).unwrap())
        });
        let aws_sign = |digest: &[u8], out: &mut [u8]| {
            let digest = Digest::import_less_safe(digest, &SHA256).unwrap();
            aws_private
                .sign_digest(&RSA_PKCS1_SHA256, &digest, out)
                .unwrap()
        };
        aws_sign(&digest, &mut out);
        assert_eq!(out, *sig);
        g.bench_function(BenchmarkId::new(AWS_LC, k), |b| {
            b.iter(|| aws_sign(black_box(&digest), &mut out))
        });
    }
    g.finish();

    let mut g = c.benchmark_group("rsa_pkcs1_verify");
    for (pkey, _, vg_public, sig, _, aws_public) in &keys {
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
        g.bench_function(BenchmarkId::new(AWS_LC, k), |b| {
            b.iter(|| {
                let digest = Digest::import_less_safe(black_box(&digest), &SHA256).unwrap();
                black_box(aws_public)
                    .verify_digest_sig(&digest, black_box(sig))
                    .unwrap()
            })
        });
    }
    g.finish();

    let mut g = c.benchmark_group("rsa_pkcs1_recover");
    for (pkey, _, vg_public, sig, _, _) in &keys {
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

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
pub fn bench(_: &mut Criterion) {}
