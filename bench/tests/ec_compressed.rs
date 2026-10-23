//! Differential checks of SEC 1 conversion against OpenSSL on every curve.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use openssl::bn::BigNumContext;
use openssl::ec::{EcGroup, EcPoint, PointConversionForm};
use openssl::nid::Nid;
use verified_garbage::ecdh::PrivateKey;

macro_rules! differential {
    ($name:ident, $curve:ident, $len:literal, $nid:ident) => {
        #[test]
        fn $name() {
            use verified_garbage::ecdh::$curve;
            let group = EcGroup::from_curve_name(Nid::$nid).unwrap();
            let mut ctx = BigNumContext::new().unwrap();
            for d in 1..=16 {
                let mut private = [0; $len];
                private[$len - 1] = d;
                let key = PrivateKey::<$curve>::from_bytes(&private);
                let public = key.public_key().unwrap();
                let point = EcPoint::from_bytes(&group, &public, &mut ctx).unwrap();
                let compressed = $curve::compress_public_key(&public).unwrap();
                assert_eq!(
                    point
                        .to_bytes(&group, PointConversionForm::COMPRESSED, &mut ctx)
                        .unwrap(),
                    compressed
                );
                assert_eq!($curve::compress_public_key(&public), Some(compressed));
                for tag in [2, 3] {
                    let mut candidate = compressed;
                    candidate[0] = tag;
                    for i in [1, $len / 2, $len] {
                        for byte in [0, 1, 127, 255] {
                            let mut mutated = candidate;
                            mutated[i] = byte;
                            let expected = EcPoint::from_bytes(&group, &mutated, &mut ctx)
                                .ok()
                                .map(|q| {
                                    q.to_bytes(&group, PointConversionForm::UNCOMPRESSED, &mut ctx)
                                        .unwrap()
                                });
                            assert_eq!(
                                $curve::decompress_public_key(&mutated).map(|q| q.to_vec()),
                                expected,
                                "d={d}, tag={tag}, byte {i}={byte}"
                            );
                        }
                    }
                }
            }
        }
    };
}

differential!(p192, P192, 24, X9_62_PRIME192V1);
differential!(p224, P224, 28, SECP224R1);
differential!(p256, P256, 32, X9_62_PRIME256V1);
differential!(p384, P384, 48, SECP384R1);
differential!(p521, P521, 66, SECP521R1);
differential!(secp256k1, Secp256k1, 32, SECP256K1);
differential!(brainpoolp256r1, BrainpoolP256r1, 32, BRAINPOOL_P256R1);
differential!(brainpoolp384r1, BrainpoolP384r1, 48, BRAINPOOL_P384R1);
differential!(brainpoolp512r1, BrainpoolP512r1, 64, BRAINPOOL_P512R1);
