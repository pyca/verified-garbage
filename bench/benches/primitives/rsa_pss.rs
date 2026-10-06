//! RSASSA-PSS with each supported hash function, MGF1 over the same one and
//! a salt as long as the hash value: signing and verifying, beside OpenSSL.

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
/// its default blinding when signing).
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use openssl::md::{Md, MdRef};
    use openssl::pkey::{PKey, Private};
    use openssl::pkey_ctx::PkeyCtx;
    use openssl::rsa::{Padding, Rsa};
    use openssl::sign::RsaPssSaltlen;
    use verified_garbage::rsa::{PrivateKey, PublicKey};
    use verified_garbage::rsa_pss::{Hash, SaltLength, sign, verify};

    use crate::{OPENSSL, VG};

    // Each supported hash function, by the name its modules have and
    // OpenSSL's.
    let hashes = [
        ("md5", Hash::Md5, "MD5"),
        ("sha1", Hash::Sha1, "SHA1"),
        ("sha224", Hash::Sha224, "SHA224"),
        ("sha256", Hash::Sha256, "SHA256"),
        ("sha384", Hash::Sha384, "SHA384"),
        ("sha512", Hash::Sha512, "SHA512"),
        ("sha512_224", Hash::Sha512_224, "SHA512-224"),
        ("sha512_256", Hash::Sha512_256, "SHA512-256"),
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
            (PKey::from_rsa(key).unwrap(), vg_private, vg_public)
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

    for (name, hash, md) in hashes {
        let md = Md::fetch(None, md, None).unwrap();
        let digest = vec![0x42; md.size()];
        let sizes = if name == "sha256" {
            &keys[..]
        } else {
            &keys[..1]
        };
        let sigs: Vec<_> = sizes
            .iter()
            .map(|(_, vg_private, _)| sign(vg_private, &digest, hash, hash, digest.len()).unwrap())
            .collect();

        let mut g = c.benchmark_group(format!("rsa_pss_{name}_mgf1_{name}_sign"));
        for ((pkey, vg_private, _), sig) in sizes.iter().zip(&sigs) {
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
        }
        g.finish();

        let mut g = c.benchmark_group(format!("rsa_pss_{name}_mgf1_{name}_verify"));
        for ((pkey, _, vg_public), sig) in sizes.iter().zip(&sigs) {
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
        }
        g.finish();
    }
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
pub fn bench(_: &mut Criterion) {}
