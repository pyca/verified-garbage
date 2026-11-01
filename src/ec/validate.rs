//! Standalone public-key validation, in one call of a verified function.

#![cfg(target_arch = "x86_64")]

use crate::cpu::detected;

use verified_garbage_cpu::Features;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Backend {
    Baseline,
    Adx,
}

impl Backend {
    fn select(cpu: Features, required: Features) -> Self {
        if cpu.contains(required) {
            Self::Adx
        } else {
            Self::Baseline
        }
    }
}

macro_rules! check {
    ($base:ident, $public:ident, $ws:ident) => {
        $base($public, &mut $ws)
    };
    ($base:ident, $public:ident, $ws:ident, $adx:ident, $features:ident) => {
        match Backend::select(detected(), $features) {
            Backend::Baseline => $base($public, &mut $ws),
            Backend::Adx => $adx($public, &mut $ws),
        }
    };
}

macro_rules! validate {
    ($curve:ident, $len:literal, $module:ident, $base:ident, [$($adx:ident, $features:ident)?]) => {
        impl super::$curve {
            /// Checks an uncompressed SEC 1 public key (`04 || x || y`).
            ///
            /// One call of verified code checks the encoding, decodes both
            /// coordinates, checks their bounds and the curve equation
            /// (SP 800-56A §5.6.2.3.3). These curves have cofactor one, so no
            /// scalar multiplication is needed. Infinity and compressed or
            /// hybrid encodings are rejected. Available on x86-64.
            pub fn validate_public_key(public: &[u8; 2 * $len + 1]) -> bool {
                use crate::arch::$module::{$base, $($adx, $features)?};
                let mut ws = [0u64; 1024];
                // SAFETY: public is readable for the complete encoding;
                // ws is a separate, writable 8192-byte Rust object. They
                // cannot overlap each other or the call's stack frame, or
                // wrap around the address space. Dispatch checks the CPU
                // features required by the selected variant.
                let ok = unsafe { check!($base, public, ws $(, $adx, $features)?) };
                // The verified contract returns exactly zero or one.
                ok == 1
            }
        }
    };
}

validate!(
    P192,
    24,
    ec_p192_validate,
    vg_ec_p192_validate_public_key,
    []
);

validate!(
    P224,
    28,
    ec_p224_validate,
    vg_ec_p224_validate_public_key,
    []
);

validate!(
    P256,
    32,
    ec_p256_validate,
    vg_ec_p256_validate_public_key,
    [
        vg_ec_p256_validate_public_key_adx,
        VG_EC_P256_VALIDATE_PUBLIC_KEY_ADX_FEATURES
    ]
);

validate!(
    P384,
    48,
    ec_p384_validate,
    vg_ec_p384_validate_public_key,
    [
        vg_ec_p384_validate_public_key_adx,
        VG_EC_P384_VALIDATE_PUBLIC_KEY_ADX_FEATURES
    ]
);

validate!(
    P521,
    66,
    ec_p521_validate,
    vg_ec_p521_validate_public_key,
    [
        vg_ec_p521_validate_public_key_adx,
        VG_EC_P521_VALIDATE_PUBLIC_KEY_ADX_FEATURES
    ]
);

validate!(
    Secp256k1,
    32,
    ec_secp256k1_validate,
    vg_ec_secp256k1_validate_public_key,
    []
);

validate!(
    BrainpoolP256r1,
    32,
    ec_brainpoolp256r1_validate,
    vg_ec_brainpoolp256r1_validate_public_key,
    []
);

validate!(
    BrainpoolP384r1,
    48,
    ec_brainpoolp384r1_validate,
    vg_ec_brainpoolp384r1_validate_public_key,
    []
);

validate!(
    BrainpoolP512r1,
    64,
    ec_brainpoolp512r1_validate,
    vg_ec_brainpoolp512r1_validate_public_key,
    []
);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ecdh::*;
    use verified_garbage_cpu::feature;

    #[test]
    fn select() {
        let required = crate::arch::ec_p256_validate::VG_EC_P256_VALIDATE_PUBLIC_KEY_ADX_FEATURES;
        for bits in [0, feature::BMI2, feature::ADX] {
            assert_eq!(Backend::select(Features(bits), required), Backend::Baseline);
        }
        assert_eq!(
            Backend::select(Features(feature::BMI2 | feature::ADX), required),
            Backend::Adx
        );
    }

    macro_rules! cases {
        ($name:ident, $curve:ident, $len:literal) => {
            #[test]
            fn $name() {
                let mut one = [0; $len];
                one[$len - 1] = 1;
                let reference = PrivateKey::<$curve>::from_bytes(&one);
                for d in 1..=8 {
                    let mut private = one;
                    private[$len - 1] = d;
                    let public = PrivateKey::<$curve>::from_bytes(&private)
                        .public_key()
                        .unwrap();
                    assert!($curve::validate_public_key(&public));
                    // Check every tag, including compressed and hybrid
                    // forms, against the uncompressed encoding requirement.
                    for tag in 0..=255 {
                        let mut q = public;
                        q[0] = tag;
                        assert_eq!($curve::validate_public_key(&q), tag == 4);
                    }
                    // Differential checks exercise decoding at every byte,
                    // field bounds, and both coordinates' curve equation.
                    for i in 1..public.len() {
                        for byte in [0, 1, 0xff] {
                            let mut q = public;
                            q[i] = byte;
                            assert_eq!(
                                $curve::validate_public_key(&q),
                                reference.diffie_hellman(&q).is_ok()
                            );
                        }
                    }
                }
                for tag in [0, 4] {
                    let mut q = [0; 2 * $len + 1];
                    q[0] = tag;
                    assert!(!$curve::validate_public_key(&q));
                    q[1..].fill(0xff);
                    assert!(!$curve::validate_public_key(&q));
                }
            }
        };
    }
    cases!(p192, P192, 24);
    cases!(p224, P224, 28);
    cases!(p256, P256, 32);
    cases!(p384, P384, 48);
    cases!(p521, P521, 66);
    cases!(secp256k1, Secp256k1, 32);
    cases!(brainpoolp256r1, BrainpoolP256r1, 32);
    cases!(brainpoolp384r1, BrainpoolP384r1, 48);
    cases!(brainpoolp512r1, BrainpoolP512r1, 64);
}
