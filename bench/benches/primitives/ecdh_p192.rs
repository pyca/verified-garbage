//! ECDH over P-192 beside OpenSSL.

use criterion::Criterion;

pub const USES: &[&str] = &["ecdh_p192", "ec_p192"];

#[cfg(any(target_arch = "x86", target_arch = "arm"))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use openssl::bn::{BigNum, BigNumContext};
    use openssl::derive::Deriver;
    use openssl::ec::{EcGroup, EcKey, EcPoint};
    use openssl::nid::Nid;
    use openssl::pkey::PKey;
    use verified_garbage::ecdh::{P192, PrivateKey};

    use crate::{OPENSSL, VG};

    // Keys below P-192's order.
    let d = [0x42; 24];
    let peer_d = [0x24; 24];
    let peer = PrivateKey::<P192>::from_bytes(&peer_d)
        .public_key()
        .unwrap();
    let group = EcGroup::from_curve_name(Nid::X9_62_PRIME192V1).unwrap();
    let mut ctx = BigNumContext::new().unwrap();
    let d_bn = BigNum::from_slice(&d).unwrap();
    let mut public = EcPoint::new(&group).unwrap();
    public.mul_generator2(&group, &d_bn, &mut ctx).unwrap();
    // Each side's private key is loaded once, outside the measurements, as a
    // party holds its key across exchanges; the peer's public key comes with
    // each exchange, and is decoded and validated in it.
    let vg_private = PrivateKey::<P192>::from_bytes(&d);
    let openssl_private =
        PKey::from_ec_key(EcKey::from_private_components(&group, &d_bn, &public).unwrap()).unwrap();
    let mut g = c.benchmark_group("ecdh_p192");
    // The ids' size is the bytes of the shared secret.
    g.bench_function(BenchmarkId::new(VG, 24), |b| {
        b.iter(|| {
            black_box(&vg_private)
                .diffie_hellman(black_box(&peer))
                .unwrap()
        })
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 24), |b| {
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

#[cfg(not(any(target_arch = "x86", target_arch = "arm")))]
pub fn bench(_: &mut Criterion) {}
