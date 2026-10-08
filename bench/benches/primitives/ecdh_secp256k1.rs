//! ECDH over secp256k1 beside OpenSSL (aws-lc-rs has no ECDH over secp256k1).

use criterion::Criterion;

pub const USES: &[&str] = &["ecdh_secp256k1", "ec_secp256k1"];

#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use openssl::bn::{BigNum, BigNumContext};
    use openssl::derive::Deriver;
    use openssl::ec::{EcGroup, EcKey, EcPoint};
    use openssl::nid::Nid;
    use openssl::pkey::PKey;
    use verified_garbage::ecdh::{PrivateKey, Secp256k1};

    use crate::{OPENSSL, VG};

    // Keys below secp256k1's order.
    let d = [0x42; 32];
    let peer_d = [0x24; 32];
    let peer = PrivateKey::<Secp256k1>::from_bytes(&peer_d)
        .public_key()
        .unwrap();
    let group = EcGroup::from_curve_name(Nid::SECP256K1).unwrap();
    let mut ctx = BigNumContext::new().unwrap();
    let d_bn = BigNum::from_slice(&d).unwrap();
    let mut public = EcPoint::new(&group).unwrap();
    public.mul_generator2(&group, &d_bn, &mut ctx).unwrap();
    // Each side's private key is loaded once, outside the measurements, as a
    // party holds its key across exchanges; the peer's public key comes with
    // each exchange, and is decoded and validated in it.
    let vg_private = PrivateKey::<Secp256k1>::from_bytes(&d);
    let openssl_private =
        PKey::from_ec_key(EcKey::from_private_components(&group, &d_bn, &public).unwrap()).unwrap();
    let mut g = c.benchmark_group("ecdh_secp256k1");
    // The ids' size is the bytes of the shared secret.
    g.bench_function(BenchmarkId::new(VG, 32), |b| {
        b.iter(|| {
            black_box(&vg_private)
                .diffie_hellman(black_box(&peer))
                .unwrap()
        })
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 32), |b| {
        b.iter(|| {
            let point = EcPoint::from_bytes(&group, black_box(&peer), &mut ctx).unwrap();
            let peer = PKey::from_ec_key(EcKey::from_public_key(&group, &point).unwrap()).unwrap();
            let mut d = Deriver::new(black_box(&openssl_private)).unwrap();
            d.set_peer(&peer).unwrap();
            d.derive_to_vec().unwrap()
        })
    });
    g.finish();
}

#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_: &mut Criterion) {}
