//! HMAC-SHA-512/224.

use criterion::Criterion;

pub const USES: &[&str] = &["hmac_sha512_224", "sha512_224", "sha512"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::sha512_224::Sha512_224;
    use verified_garbage::hmac::Hmac;

    // aws-lc-rs has no HMAC with SHA-512/224.
    let md = MessageDigest::from_name("SHA512-224").unwrap();
    crate::hmac_group(c, "hmac-sha512-224", Hmac::<Sha512_224>::mac, md, None);
    crate::hmac_verify_group::<Sha512_224>(c, "hmac-sha512-224-verify", md, None);
    probe(c);
}

// EXPERIMENT (not for merge): each HMAC of the SHA-512 family from three
// call sites of its own, at 64 bytes and 16 KiB. Id: variant (1 SHA-384,
// 2 SHA-512, 3 SHA-512/224, 4 SHA-512/256, 5 SHA-256, 6 SHA-224) * 1000000
// + site * 100000 + size.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
fn probe(c: &mut Criterion) {
    use criterion::BenchmarkId;
    use std::hint::black_box;
    use verified_garbage::hashes::sha224::Sha224;
    use verified_garbage::hashes::sha256::Sha256;
    use verified_garbage::hashes::sha384::Sha384;
    use verified_garbage::hashes::sha512::Sha512;
    use verified_garbage::hashes::sha512_224::Sha512_224;
    use verified_garbage::hashes::sha512_256::Sha512_256;
    use verified_garbage::hmac::Hmac;

    let key = [0x0b; 32];
    let mut g = c.benchmark_group("hmacprobe");
    for size in [64usize, 16384] {
        let data = vec![0x5a; size];
        macro_rules! site {
            ($v:expr, $s:expr, $h:ty) => {
                g.bench_function(BenchmarkId::new("verified-garbage", $v * 1000000 + $s * 100000 + size), |b| {
                    b.iter(|| Hmac::<$h>::mac(black_box(&key), black_box(&data)))
                });
            };
        }
        site!(1, 1, Sha384);
        site!(2, 1, Sha512);
        site!(3, 1, Sha512_224);
        site!(4, 1, Sha512_256);
        site!(5, 1, Sha256);
        site!(6, 1, Sha224);
        site!(1, 2, Sha384);
        site!(2, 2, Sha512);
        site!(3, 2, Sha512_224);
        site!(4, 2, Sha512_256);
        site!(5, 2, Sha256);
        site!(6, 2, Sha224);
        site!(1, 3, Sha384);
        site!(2, 3, Sha512);
        site!(3, 3, Sha512_224);
        site!(4, 3, Sha512_256);
        site!(5, 3, Sha256);
        site!(6, 3, Sha224);
    }
    g.finish();
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
fn probe(_: &mut Criterion) {}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
)))]
pub fn bench(_: &mut Criterion) {}
