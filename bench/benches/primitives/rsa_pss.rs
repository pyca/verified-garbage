//! RSASSA-PSS with each supported hash function, MGF1 over the same one and
//! a salt as long as the hash value: signing and verifying, beside OpenSSL
//! and, for SHA-256, SHA-384 and SHA-512, aws-lc-rs.

use criterion::Criterion;

/// The module `rsa_pss`, each hash function's Rust module (`rsa_pss_<H>`,
/// `src/rsa_pss/<H>.rs`) and its generated one
/// (`rsa_pss_<H>_mgf1_<H>`), and the modules they call.
pub const USES: &[&str] = &[
    "rsa_pss",
    "rsa_pss_md5",
    "rsa_pss_md5_mgf1_md5",
    "rsa_pss_sha1",
    "rsa_pss_sha1_mgf1_sha1",
    "rsa_pss_sha224",
    "rsa_pss_sha224_mgf1_sha224",
    "rsa_pss_sha256",
    "rsa_pss_sha256_mgf1_sha256",
    "rsa_pss_sha384",
    "rsa_pss_sha384_mgf1_sha384",
    "rsa_pss_sha512",
    "rsa_pss_sha512_mgf1_sha512",
    "rsa_pss_sha512_224",
    "rsa_pss_sha512_224_mgf1_sha512_224",
    "rsa_pss_sha512_256",
    "rsa_pss_sha512_256_mgf1_sha512_256",
    "rsa",
    "md5",
    "sha1",
    "sha224",
    "sha256",
    "sha384",
    "sha512",
    "sha512_224",
    "sha512_256",
];

/// Every hash function with a modulus of 2048 bits, and SHA-256 with
/// moduli of 3072 and 4096 bits too, all with the exponent 65537, in the
/// groups `rsa_pss_<H>_mgf1_<H>_sign` and `_verify`; the ids' size is the
/// modulus' bytes. Each library loads the key once, outside the
/// measurements, and is given the hash value (OpenSSL through
/// `EVP_PKEY_sign` and `EVP_PKEY_verify` with PSS padding, the hash function
/// as the hash and MGF1's hash, and a salt as long as the hash value, with
/// its default blinding when signing; aws-lc-rs through
/// `KeyPair::sign_digest` and `ParsedPublicKey::verify_digest_sig`, which set
/// up an `EVP_PKEY_CTX` in every operation and take a salt as long as the
/// hash value, from a key loaded from its components). Signatures are
/// randomized, so aws-lc-rs and verified-garbage verify each other's.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use aws_lc_rs::digest::{self, Digest};
    use aws_lc_rs::rsa::KeyPairComponents;
    use aws_lc_rs::signature::{
        self as aws_sig, ParsedPublicKey, RsaKeyPair, RsaPublicKeyComponents,
    };
    use criterion::BenchmarkId;
    use openssl::md::{Md, MdRef};
    use openssl::pkey::{PKey, Private};
    use openssl::pkey_ctx::PkeyCtx;
    use openssl::rsa::{Padding, Rsa};
    use openssl::sign::RsaPssSaltlen;
    use verified_garbage::rsa::{PrivateKey, PublicKey};
    use verified_garbage::rsa_pss::{Hash, SaltLength, sign, verify};

    use crate::{AWS_LC, OPENSSL, VG};

    // Each supported hash function, by the name its modules have and
    // OpenSSL's, and, if aws-lc-rs has it, its hash function, signing
    // encoding and verification parameters.
    let hashes = [
        ("md5", Hash::Md5, "MD5", None),
        ("sha1", Hash::Sha1, "SHA1", None),
        ("sha224", Hash::Sha224, "SHA224", None),
        (
            "sha256",
            Hash::Sha256,
            "SHA256",
            Some((
                &digest::SHA256,
                &aws_sig::RSA_PSS_SHA256,
                &aws_sig::RSA_PSS_2048_8192_SHA256,
            )),
        ),
        (
            "sha384",
            Hash::Sha384,
            "SHA384",
            Some((
                &digest::SHA384,
                &aws_sig::RSA_PSS_SHA384,
                &aws_sig::RSA_PSS_2048_8192_SHA384,
            )),
        ),
        (
            "sha512",
            Hash::Sha512,
            "SHA512",
            Some((
                &digest::SHA512,
                &aws_sig::RSA_PSS_SHA512,
                &aws_sig::RSA_PSS_2048_8192_SHA512,
            )),
        ),
        ("sha512_224", Hash::Sha512_224, "SHA512-224", None),
        ("sha512_256", Hash::Sha512_256, "SHA512-256", None),
    ];
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
            (
                PKey::from_rsa(key).unwrap(),
                vg_private,
                vg_public,
                aws_private,
                (n, e),
            )
        })
        .collect();
    let ctx = |pkey: &PKey<Private>, md: &MdRef, init: fn(&mut PkeyCtx<_>)| {
        let mut ctx = PkeyCtx::new(pkey).unwrap();
        init(&mut ctx);
        ctx.set_rsa_padding(Padding::PKCS1_PSS).unwrap();
        ctx.set_signature_md(md).unwrap();
        ctx.set_rsa_mgf1_md(md).unwrap();
        ctx.set_rsa_pss_saltlen(RsaPssSaltlen::DIGEST_LENGTH)
            .unwrap();
        ctx
    };

    for (name, hash, md, aws_lc) in hashes {
        let md = Md::fetch(None, md, None).unwrap();
        let digest = vec![0x42; md.size()];
        let sizes = if name == "sha256" {
            &keys[..]
        } else {
            &keys[..1]
        };
        let sigs: Vec<_> = sizes
            .iter()
            .map(|(_, vg_private, ..)| sign(vg_private, &digest, hash, hash, digest.len()).unwrap())
            .collect();
        // aws-lc-rs's public keys, loaded from `(n, e)` for the hash's
        // parameters.
        let aws_public: Vec<Option<ParsedPublicKey>> = sizes
            .iter()
            .map(|(.., (n, e))| {
                aws_lc.map(|(_, _, params)| {
                    RsaPublicKeyComponents { n, e }
                        .to_parsed_public_key(params)
                        .unwrap()
                })
            })
            .collect();

        let mut g = c.benchmark_group(format!("rsa_pss_{name}_mgf1_{name}_sign"));
        for (((pkey, vg_private, vg_public, aws_private, _), sig), aws_public) in
            sizes.iter().zip(&sigs).zip(&aws_public)
        {
            let k = sig.len();
            g.bench_function(BenchmarkId::new(VG, k), |b| {
                b.iter(|| {
                    sign(
                        black_box(vg_private),
                        black_box(&digest),
                        hash,
                        hash,
                        digest.len(),
                    )
                    .unwrap()
                })
            });
            let mut c = ctx(pkey, &md, |c| c.sign_init().unwrap());
            let mut out = vec![0; k];
            g.bench_function(BenchmarkId::new(OPENSSL, k), |b| {
                b.iter(|| c.sign(black_box(&digest), Some(&mut out)).unwrap())
            });
            if let (Some((alg, encoding, _)), Some(aws_public)) = (aws_lc, aws_public) {
                let aws_sign = |digest: &[u8], out: &mut [u8]| {
                    let digest = Digest::import_less_safe(digest, alg).unwrap();
                    aws_private.sign_digest(encoding, &digest, out).unwrap()
                };
                // Each verifies the other's signature.
                aws_sign(&digest, &mut out);
                let d = Digest::import_less_safe(&digest, alg).unwrap();
                aws_public.verify_digest_sig(&d, sig).unwrap();
                assert!(verify(
                    vg_public,
                    &out,
                    &digest,
                    hash,
                    hash,
                    SaltLength::Len(digest.len())
                ));
                g.bench_function(BenchmarkId::new(AWS_LC, k), |b| {
                    b.iter(|| aws_sign(black_box(&digest), &mut out))
                });
            }
        }
        g.finish();

        let mut g = c.benchmark_group(format!("rsa_pss_{name}_mgf1_{name}_verify"));
        for (((pkey, _, vg_public, ..), sig), aws_public) in
            sizes.iter().zip(&sigs).zip(&aws_public)
        {
            let k = sig.len();
            g.bench_function(BenchmarkId::new(VG, k), |b| {
                b.iter(|| {
                    assert!(verify(
                        black_box(vg_public),
                        black_box(sig),
                        &digest,
                        hash,
                        hash,
                        SaltLength::Len(digest.len())
                    ))
                })
            });
            let mut c = ctx(pkey, &md, |c| c.verify_init().unwrap());
            g.bench_function(BenchmarkId::new(OPENSSL, k), |b| {
                b.iter(|| assert!(c.verify(black_box(&digest), black_box(sig)).unwrap()))
            });
            if let (Some((alg, ..)), Some(aws_public)) = (aws_lc, aws_public) {
                g.bench_function(BenchmarkId::new(AWS_LC, k), |b| {
                    b.iter(|| {
                        let digest = Digest::import_less_safe(black_box(&digest), alg).unwrap();
                        black_box(aws_public)
                            .verify_digest_sig(&digest, black_box(sig))
                            .unwrap()
                    })
                });
            }
        }
        g.finish();
    }
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
pub fn bench(_: &mut Criterion) {}
