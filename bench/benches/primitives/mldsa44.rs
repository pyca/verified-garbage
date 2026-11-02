//! ML-DSA-44: key generation from a seed, signing and verification, beside
//! aws-lc-rs and OpenSSL.
//!
//! OpenSSL implements ML-DSA from version 3.5; the runners use 3.0.
//! Enable `openssl-mldsa` on a supported host for the comparison. The ids'
//! sizes are the output bytes for keygen/sign and message bytes for verify.
//! Signing has an empty context. Each signing iteration signs the next of
//! `MESSAGES` messages, the same for every library, since the number of
//! times the rejection loop runs depends on the message (and, hedged, on the
//! randomness): averaged over them, a comparison measures each library's
//! loop rather than one message's luck. `mldsa44_sign` signs hedged, with
//! fresh randomness, in every library; `mldsa44_sign_deterministic` is
//! verified-garbage's deterministic signing (`rnd` all zeros), whose time
//! for the same messages repeats exactly from run to run.

use criterion::Criterion;

pub const USES: &[&str] = &["mldsa44", "mldsa_common", "mldsa", "sha3"];

/// How many messages signing cycles through.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]
const MESSAGES: usize = 256;

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use aws_lc_rs::signature::{
        KeyPair, ML_DSA_44, ML_DSA_44_SIGNING, ParsedPublicKey, PqdsaKeyPair,
    };
    use criterion::BenchmarkId;
    use verified_garbage::mldsa44::SigningKey44;

    use crate::{AWS_LC, BenchDyn, VG};

    let seed = [0x42; 32];
    let key = SigningKey44::from_seed(&seed).unwrap();
    let msg = [0x5a; 64];
    // The messages that signing cycles through.
    let msgs: [[u8; 64]; MESSAGES] = core::array::from_fn(|i| [i as u8; 64]);
    // Keep verification inputs identical across benchmark processes and revisions.
    let sig = key.sign_deterministic(&msg, b"").unwrap();
    let aws_lc_key = PqdsaKeyPair::from_seed(&ML_DSA_44_SIGNING, &seed).unwrap();
    assert_eq!(
        aws_lc_key.public_key().as_ref(),
        key.verifying_key().as_bytes()
    );
    let aws_lc_public = ParsedPublicKey::new(&ML_DSA_44, key.verifying_key().as_bytes()).unwrap();
    aws_lc_public.verify_sig(&msg, &sig).unwrap();
    let mut aws_lc_sig = [0u8; 2420];
    aws_lc_key.sign(&msg, &mut aws_lc_sig).unwrap();
    key.verifying_key().verify(&msg, b"", &aws_lc_sig).unwrap();
    #[cfg(feature = "openssl-mldsa")]
    let (openssl_key, openssl_public) = {
        use openssl::pkey::{KeyType, PKey};
        use openssl::sign::{Signer, Verifier};

        let key_type = KeyType::ML_DSA_44;
        let openssl_key = PKey::private_key_from_seed(None, key_type, None, &seed).unwrap();
        let public = openssl_key.raw_public_key().unwrap();
        assert_eq!(public.as_slice(), key.verifying_key().as_bytes());
        let openssl_public =
            PKey::public_key_from_raw_bytes_ex(None, key_type, None, &public).unwrap();
        assert!(
            Verifier::new_without_digest(&openssl_public)
                .unwrap()
                .verify_oneshot(&sig, &msg)
                .unwrap()
        );
        let openssl_sig = Signer::new_without_digest(&openssl_key)
            .unwrap()
            .sign_oneshot_to_vec(&msg)
            .unwrap();
        key.verifying_key()
            .verify(&msg, b"", openssl_sig.as_slice().try_into().unwrap())
            .unwrap();
        (openssl_key, openssl_public)
    };
    let mut g = c.benchmark_group("mldsa44_keygen");
    g.bench(BenchmarkId::new(VG, 1312 + 32), |b| {
        b.iter(|| SigningKey44::from_seed(black_box(&seed)).unwrap())
    });
    #[cfg(feature = "openssl-mldsa")]
    g.bench(BenchmarkId::new(crate::OPENSSL, 1344), |b| {
        b.iter(|| {
            openssl::pkey::PKey::private_key_from_seed(
                None,
                openssl::pkey::KeyType::ML_DSA_44,
                None,
                black_box(&seed),
            )
            .unwrap()
            .raw_public_key()
            .unwrap()
        })
    });
    // aws-lc-rs encodes the public key when it constructs the key pair.
    g.bench(BenchmarkId::new(AWS_LC, 1344), |b| {
        b.iter(|| PqdsaKeyPair::from_seed(&ML_DSA_44_SIGNING, black_box(&seed)).unwrap())
    });
    g.finish();
    let mut g = c.benchmark_group("mldsa44_sign");
    let mut i = 0;
    g.bench(BenchmarkId::new(VG, 2420), |b| {
        b.iter(|| {
            i = (i + 1) % MESSAGES;
            key.sign(black_box(&msgs[i]), b"").unwrap()
        })
    });
    #[cfg(feature = "openssl-mldsa")]
    g.bench(BenchmarkId::new(crate::OPENSSL, 2420), |b| {
        b.iter(|| {
            i = (i + 1) % MESSAGES;
            openssl::sign::Signer::new_without_digest(&openssl_key)
                .unwrap()
                .sign_oneshot_to_vec(black_box(&msgs[i]))
                .unwrap()
        })
    });
    g.bench(BenchmarkId::new(AWS_LC, 2420), |b| {
        b.iter(|| {
            i = (i + 1) % MESSAGES;
            aws_lc_key
                .sign(black_box(&msgs[i]), &mut aws_lc_sig)
                .unwrap()
        })
    });
    g.finish();
    let mut g = c.benchmark_group("mldsa44_sign_deterministic");
    g.bench(BenchmarkId::new(VG, 2420), |b| {
        b.iter(|| {
            i = (i + 1) % MESSAGES;
            key.sign_deterministic(black_box(&msgs[i]), b"").unwrap()
        })
    });
    g.finish();
    let mut g = c.benchmark_group("mldsa44_verify");
    g.bench(BenchmarkId::new(VG, 64), |b| {
        b.iter(|| {
            key.verifying_key()
                .verify(black_box(&msg), b"", &sig)
                .unwrap()
        })
    });
    #[cfg(feature = "openssl-mldsa")]
    g.bench(BenchmarkId::new(crate::OPENSSL, 64), |b| {
        b.iter(|| {
            assert!(
                openssl::sign::Verifier::new_without_digest(&openssl_public)
                    .unwrap()
                    .verify_oneshot(black_box(&sig), black_box(&msg))
                    .unwrap()
            )
        })
    });
    g.bench(BenchmarkId::new(AWS_LC, 64), |b| {
        b.iter(|| {
            aws_lc_public
                .verify_sig(black_box(&msg), black_box(&sig))
                .unwrap()
        })
    });
    g.finish();
    // Precomputed message representatives exclude hashing from the timing.
    let mu = [0x5a; 64];
    let rnd = [0x42; 32];
    let mu_sig = key.sign_mu(&mu, &rnd).unwrap();
    let mut g = c.benchmark_group("mldsa44_sign_mu");
    g.bench(BenchmarkId::new(VG, mu_sig.len()), |b| {
        b.iter(|| key.sign_mu(black_box(&mu), black_box(&rnd)).unwrap())
    });
    g.finish();
    let mut g = c.benchmark_group("mldsa44_verify_mu");
    g.bench(BenchmarkId::new(VG, 64), |b| {
        b.iter(|| {
            key.verifying_key()
                .verify_mu(black_box(&mu), black_box(&mu_sig))
                .unwrap()
        })
    });
    g.finish();
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
)))]
pub fn bench(_: &mut Criterion) {}
