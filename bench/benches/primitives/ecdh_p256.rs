//! ECDH over P-256 beside OpenSSL and aws-lc-rs.

use criterion::Criterion;

pub const USES: &[&str] = &["ecdh_p256", "ec_p256"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]
pub fn bench(c: &mut Criterion) {
    experimental_corpus::check();
    experimental_corpus::bench(c);
    use std::hint::black_box;

    use aws_lc_rs::agreement::{self, UnparsedPublicKey};
    use aws_lc_rs::error::Unspecified;
    use criterion::BenchmarkId;
    use openssl::bn::{BigNum, BigNumContext};
    use openssl::derive::Deriver;
    use openssl::ec::{EcGroup, EcKey, EcPoint};
    use openssl::nid::Nid;
    use openssl::pkey::PKey;
    use verified_garbage::ecdh::{P256, PrivateKey};

    use crate::{AWS_LC, OPENSSL, VG};

    let d = [0x42; 32];
    let peer = PrivateKey::<P256>::from_bytes(&[0x24; 32])
        .public_key()
        .unwrap();
    let group = EcGroup::from_curve_name(Nid::X9_62_PRIME256V1).unwrap();
    let mut ctx = BigNumContext::new().unwrap();
    let d_bn = BigNum::from_slice(&d).unwrap();
    let mut public = EcPoint::new(&group).unwrap();
    public.mul_generator2(&group, &d_bn, &mut ctx).unwrap();
    // Each side's private key is loaded once, outside the measurements, as a
    // party holds its key across exchanges; the peer's public key comes with
    // each exchange, and is decoded and validated in it.
    let vg_private = PrivateKey::<P256>::from_bytes(&d);
    let openssl_private =
        PKey::from_ec_key(EcKey::from_private_components(&group, &d_bn, &public).unwrap()).unwrap();
    let aws_lc_private =
        agreement::PrivateKey::from_private_key(&agreement::ECDH_P256, &d).unwrap();
    // aws-lc-rs decodes and validates the peer's public key in `agree`.
    let aws_lc_agree = |private: &agreement::PrivateKey, peer: &[u8]| {
        agreement::agree(
            private,
            UnparsedPublicKey::new(&agreement::ECDH_P256, peer),
            Unspecified,
            |s| Ok(s.to_vec()),
        )
        .unwrap()
    };
    assert_eq!(
        aws_lc_agree(&aws_lc_private, &peer),
        vg_private.diffie_hellman(&peer).unwrap()
    );
    let mut g = c.benchmark_group("ecdh_p256");
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
    g.bench_function(BenchmarkId::new(AWS_LC, 32), |b| {
        b.iter(|| aws_lc_agree(black_box(&aws_lc_private), black_box(&peer)))
    });
    g.finish();
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
)))]
pub fn bench(_: &mut Criterion) {}

mod experimental_corpus {
use aws_lc_rs::agreement::{self, UnparsedPublicKey};
use aws_lc_rs::error::Unspecified;
use verified_garbage::ecdh::{P256,PrivateKey};
use std::hint::black_box;
fn agree(k:&agreement::PrivateKey,p:&[u8])->Vec<u8>{
    agreement::agree(k,UnparsedPublicKey::new(&agreement::ECDH_P256,p),Unspecified,|s|Ok(s.to_vec())).unwrap()
}
fn scalars()->Vec<[u8;32]>{
    let mut out=Vec::new();
    for i in 1u64..=1024 {let mut k=[0;32];k[24..].copy_from_slice(&i.to_be_bytes());out.push(k);}
    let n:[u8;32]=[0xff,0xff,0xff,0xff,0,0,0,0,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xbc,0xe6,0xfa,0xad,0xa7,0x17,0x9e,0x84,0xf3,0xb9,0xca,0xc2,0xfc,0x63,0x25,0x51];
    let mut k=n;
    for _ in 0..1024 {for b in k.iter_mut().rev(){let (v,carry)=b.overflowing_sub(1);*b=v;if !carry {break;}}out.push(k);}
    let mut rng=0x91fa_675a_239d_0321u64;
    for _ in 0..1024 {let mut k=[0;32];for chunk in k.chunks_mut(8){rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;chunk.copy_from_slice(&rng.to_be_bytes());}k[0]&=0x7f;out.push(k);}
    out
}
pub fn check(){
 let keys=scalars();
 let peers:Vec<_>=keys[2048..2064].iter().map(|k|PrivateKey::<P256>::from_bytes(k).public_key().unwrap()).collect();
 for (i,k) in keys.iter().enumerate(){let p=&peers[i%peers.len()];let a=agreement::PrivateKey::from_private_key(&agreement::ECDH_P256,k).unwrap();assert_eq!(PrivateKey::<P256>::from_bytes(k).diffie_hellman(p).unwrap().as_slice(),agree(&a,p),"scalar {i}");}
 for k in [[0u8;32],[0xffu8;32]] {assert!(PrivateKey::<P256>::from_bytes(&k).diffie_hellman(&peers[0]).is_err());}
 let mut bad=peers[0];bad[0]=5;assert!(PrivateKey::<P256>::from_bytes(&keys[0]).diffie_hellman(&bad).is_err());
 eprintln!("ECDH differential checks passed: {} scalars, 16 peers, invalid inputs",keys.len());
}
pub fn bench(c:&mut criterion::Criterion){
 let ks=scalars();let ks=&ks[2048..2304];
 let peers:Vec<_>=ks.iter().map(|k|PrivateKey::<P256>::from_bytes(k).public_key().unwrap()).collect();
 let vg:Vec<_>=ks.iter().map(PrivateKey::<P256>::from_bytes).collect();
 let aws:Vec<_>=ks.iter().map(|k|agreement::PrivateKey::from_private_key(&agreement::ECDH_P256,k).unwrap()).collect();
 let mut g=c.benchmark_group("ecdh_p256_rotating256");
 let mut i=0usize;g.bench_function(criterion::BenchmarkId::new("verified-garbage",32),|b|b.iter(||{i=(i+1)&255;black_box(&vg[i]).diffie_hellman(black_box(&peers[(i+17)&255])).unwrap()}));
 let mut i=0usize;g.bench_function(criterion::BenchmarkId::new("aws-lc-rs",32),|b|b.iter(||{i=(i+1)&255;agree(black_box(&aws[i]),black_box(&peers[(i+17)&255]))}));
 g.finish();
}

}
