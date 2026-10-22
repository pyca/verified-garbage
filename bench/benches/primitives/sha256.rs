//! SHA-256.

use std::hint::black_box;

use criterion::{BenchmarkId, Criterion};
use openssl::hash::{Hasher, MessageDigest};
use verified_garbage::hashes::sha256::Sha256;

use crate::{AWS_LC, OPENSSL, VG, hash_group_sizes};

pub const USES: &[&str] = &["sha256"];

/// `SIZES` and the short messages a TLS 1.3 handshake hashes (the
/// transcript's messages, `HKDF-Expand-Label`'s inputs): one block or two,
/// around the 55/56-byte boundary at which the padding takes a second block,
/// up to four blocks.
const SHA256_SIZES: [usize; 10] = [32, 55, 56, 64, 100, 128, 192, 256, 1024, 16384];

pub fn bench(c: &mut Criterion) {
    hash_group_sizes(
        c,
        "sha256",
        &SHA256_SIZES,
        Sha256::digest,
        MessageDigest::sha256(),
        Some(&aws_lc_rs::digest::SHA256),
    );
    transcript(c);
}

/// A TLS 1.3 handshake's transcript, as rustls hashes it: each message in
/// turn (ClientHello, ServerHello, EncryptedExtensions, Certificate,
/// CertificateVerify, the server's and the client's Finished), with the
/// hash of the transcript so far taken, from a copy of the state, after
/// ServerHello, CertificateVerify and each Finished (the key schedule's and
/// Finished's inputs).
const TRANSCRIPT: [(usize, bool); 7] = [
    (512, false),
    (122, true),
    (10, false),
    (1300, false),
    (264, true),
    (52, true),
    (52, true),
];

/// The transcript's length, which names its benchmarks.
const TRANSCRIPT_LEN: usize = {
    let mut n = 0;
    let mut i = 0;
    while i < TRANSCRIPT.len() {
        n += TRANSCRIPT[i].0;
        i += 1;
    }
    n
};

/// The last of the transcript's hashes, by `update` and a clone's `finalize`.
fn vg_transcript(msgs: &[Vec<u8>]) -> [u8; 32] {
    let mut h = Sha256::new();
    let mut last = [0; 32];
    for (m, &(_, fork)) in msgs.iter().zip(&TRANSCRIPT) {
        h.update(black_box(m));
        if fork {
            last = h.clone().finalize();
        }
    }
    last
}

/// As `vg_transcript`, with a clone of OpenSSL's `Hasher`, finished.
fn openssl_transcript(msgs: &[Vec<u8>]) -> Vec<u8> {
    let mut h = Hasher::new(MessageDigest::sha256()).unwrap();
    let mut last = Vec::new();
    for (m, &(_, fork)) in msgs.iter().zip(&TRANSCRIPT) {
        h.update(black_box(m)).unwrap();
        if fork {
            last = h.clone().finish().unwrap().to_vec();
        }
    }
    last
}

/// As `vg_transcript`, with a clone of aws-lc-rs's `Context`, finished.
fn aws_lc_transcript(msgs: &[Vec<u8>]) -> Vec<u8> {
    let mut h = aws_lc_rs::digest::Context::new(&aws_lc_rs::digest::SHA256);
    let mut last = Vec::new();
    for (m, &(_, fork)) in msgs.iter().zip(&TRANSCRIPT) {
        h.update(black_box(m));
        if fork {
            last = h.clone().finish().as_ref().to_vec();
        }
    }
    last
}

/// The transcript's hashes against OpenSSL's and aws-lc-rs's incremental
/// hashing.
fn transcript(c: &mut Criterion) {
    let msgs: Vec<Vec<u8>> = TRANSCRIPT.iter().map(|&(n, _)| vec![0x5a; n]).collect();
    assert_eq!(openssl_transcript(&msgs), vg_transcript(&msgs));
    assert_eq!(aws_lc_transcript(&msgs), vg_transcript(&msgs));
    let mut g = c.benchmark_group("sha256-transcript");
    g.bench_function(BenchmarkId::new(VG, TRANSCRIPT_LEN), |b| {
        b.iter(|| vg_transcript(&msgs))
    });
    g.bench_function(BenchmarkId::new(OPENSSL, TRANSCRIPT_LEN), |b| {
        b.iter(|| openssl_transcript(&msgs))
    });
    g.bench_function(BenchmarkId::new(AWS_LC, TRANSCRIPT_LEN), |b| {
        b.iter(|| aws_lc_transcript(&msgs))
    });
    g.finish();
}
