//! Validated SEC 1 conversion, each in one call of a verified function.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

#[cfg(any(target_arch = "x86_64", target_arch = "arm"))]
use crate::cpu::detected;
#[cfg(any(target_arch = "x86_64", target_arch = "arm"))]
use verified_garbage_cpu::Features;

/// The baseline implementation, or its variant (x86-64's `_adx`, ARMv7's
/// `_umaal`) on CPUs with the features its `_FEATURES` constant names.
#[cfg(any(target_arch = "x86_64", target_arch = "arm"))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Backend {
    Baseline,
    Fast,
}

#[cfg(any(target_arch = "x86_64", target_arch = "arm"))]
impl Backend {
    fn select(cpu: Features, required: Features) -> Self {
        if cpu.contains(required) {
            Self::Fast
        } else {
            Self::Baseline
        }
    }
}

macro_rules! check {
    ($base:ident, $out:ident, $public:ident, $ws:ident) => {
        $base(&mut $out, $public, &mut $ws)
    };
    ($base:ident, $out:ident, $public:ident, $ws:ident, $adx:ident, $features:ident) => {{
        #[cfg(target_arch = "x86_64")]
        {
            match Backend::select(detected(), $features) {
                Backend::Baseline => $base(&mut $out, $public, &mut $ws),
                Backend::Fast => $adx(&mut $out, $public, &mut $ws),
            }
        }
        #[cfg(not(target_arch = "x86_64"))]
        {
            $base(&mut $out, $public, &mut $ws)
        }
    }};
    ($base:ident, $out:ident, $public:ident, $ws:ident, umaal: $umaal:ident, $ufeatures:ident) => {{
        #[cfg(target_arch = "arm")]
        {
            match Backend::select(detected(), $ufeatures) {
                Backend::Baseline => $base(&mut $out, $public, &mut $ws),
                Backend::Fast => $umaal(&mut $out, $public, &mut $ws),
            }
        }
        #[cfg(not(target_arch = "arm"))]
        {
            $base(&mut $out, $public, &mut $ws)
        }
    }};
    ($base:ident, $out:ident, $public:ident, $ws:ident, $adx:ident, $features:ident,
        umaal: $umaal:ident, $ufeatures:ident) => {{
        #[cfg(target_arch = "x86_64")]
        {
            match Backend::select(detected(), $features) {
                Backend::Baseline => $base(&mut $out, $public, &mut $ws),
                Backend::Fast => $adx(&mut $out, $public, &mut $ws),
            }
        }
        #[cfg(target_arch = "arm")]
        {
            match Backend::select(detected(), $ufeatures) {
                Backend::Baseline => $base(&mut $out, $public, &mut $ws),
                Backend::Fast => $umaal(&mut $out, $public, &mut $ws),
            }
        }
        #[cfg(not(any(target_arch = "x86_64", target_arch = "arm")))]
        {
            $base(&mut $out, $public, &mut $ws)
        }
    }};
}

macro_rules! codec {
    ($curve:ident, $len:literal, $module:ident, $compress:ident, $decompress:ident,
        [$($compress_adx:ident, $decompress_adx:ident, $features:ident)?]
        $([$compress_umaal:ident, $decompress_umaal:ident, $cfeatures:ident, $dfeatures:ident])?) => {
        impl super::$curve {
            /// Validates and compresses `04 || x || y` to SEC 1 `02/03 || x`.
            ///
            /// Returns `None` for an invalid encoding or curve point.
            /// Infinity and hybrid encodings are rejected.
            pub fn compress_public_key(public: &[u8; 2 * $len + 1]) -> Option<[u8; $len + 1]> {
                use crate::arch::$module::$compress;
                $(#[cfg(target_arch = "x86_64")]
                use crate::arch::$module::{$compress_adx, $features};)?
                $(#[cfg(target_arch = "arm")]
                use crate::arch::$module::{$compress_umaal, $cfeatures};)?
                let mut out = [0; $len + 1];
                let mut ws = [0u64; 1024];
                // SAFETY: all three arrays have the contract's lengths and
                // occupy separate Rust objects. Their ranges cannot wrap or
                // overlap the return address. Dispatch checks CPU requirements.
                let ok = unsafe {
                    check!($compress, out, public, ws $(, $compress_adx, $features)?
                        $(, umaal: $compress_umaal, $cfeatures)?)
                };
                (ok == 1).then_some(out)
            }

            /// Validates and decompresses SEC 1 `02/03 || x` to `04 || x || y`.
            ///
            /// Returns `None` if no finite curve point has the encoded x and
            /// parity. Infinity and hybrid encodings are rejected.
            /// Timing may depend on these public input bytes.
            pub fn decompress_public_key(public: &[u8; $len + 1]) -> Option<[u8; 2 * $len + 1]> {
                use crate::arch::$module::$decompress;
                $(#[cfg(target_arch = "x86_64")]
                use crate::arch::$module::{$decompress_adx, $features};)?
                $(#[cfg(target_arch = "arm")]
                use crate::arch::$module::{$decompress_umaal, $dfeatures};)?
                let mut out = [0; 2 * $len + 1];
                let mut ws = [0u64; 1024];
                // SAFETY: all three arrays have the contract's lengths and
                // occupy separate Rust objects. Their ranges cannot wrap or
                // overlap the return address. Dispatch checks CPU requirements.
                let ok = unsafe {
                    check!($decompress, out, public, ws $(, $decompress_adx, $features)?
                        $(, umaal: $decompress_umaal, $dfeatures)?)
                };
                (ok == 1).then_some(out)
            }
        }
    };
}

#[cfg(not(target_arch = "riscv64"))]
codec!(
    P192,
    24,
    ec_p192_compressed,
    vg_ec_p192_compress_public_key,
    vg_ec_p192_decompress_public_key,
    []
);
#[cfg(not(target_arch = "riscv64"))]
codec!(
    P224,
    28,
    ec_p224_compressed,
    vg_ec_p224_compress_public_key,
    vg_ec_p224_decompress_public_key,
    []
    [
        vg_ec_p224_compress_public_key_umaal,
        vg_ec_p224_decompress_public_key_umaal,
        VG_EC_P224_COMPRESS_PUBLIC_KEY_UMAAL_FEATURES,
        VG_EC_P224_DECOMPRESS_PUBLIC_KEY_UMAAL_FEATURES
    ]
);
codec!(
    P256,
    32,
    ec_p256_compressed,
    vg_ec_p256_compress_public_key,
    vg_ec_p256_decompress_public_key,
    [
        vg_ec_p256_compress_public_key_adx,
        vg_ec_p256_decompress_public_key_adx,
        VG_EC_P256_COMPRESS_PUBLIC_KEY_ADX_FEATURES
    ]
    [
        vg_ec_p256_compress_public_key_umaal,
        vg_ec_p256_decompress_public_key_umaal,
        VG_EC_P256_COMPRESS_PUBLIC_KEY_UMAAL_FEATURES,
        VG_EC_P256_DECOMPRESS_PUBLIC_KEY_UMAAL_FEATURES
    ]
);
codec!(
    P384,
    48,
    ec_p384_compressed,
    vg_ec_p384_compress_public_key,
    vg_ec_p384_decompress_public_key,
    [
        vg_ec_p384_compress_public_key_adx,
        vg_ec_p384_decompress_public_key_adx,
        VG_EC_P384_COMPRESS_PUBLIC_KEY_ADX_FEATURES
    ]
    [
        vg_ec_p384_compress_public_key_umaal,
        vg_ec_p384_decompress_public_key_umaal,
        VG_EC_P384_COMPRESS_PUBLIC_KEY_UMAAL_FEATURES,
        VG_EC_P384_DECOMPRESS_PUBLIC_KEY_UMAAL_FEATURES
    ]
);
#[cfg(not(target_arch = "riscv64"))]
codec!(
    P521,
    66,
    ec_p521_compressed,
    vg_ec_p521_compress_public_key,
    vg_ec_p521_decompress_public_key,
    [
        vg_ec_p521_compress_public_key_adx,
        vg_ec_p521_decompress_public_key_adx,
        VG_EC_P521_COMPRESS_PUBLIC_KEY_ADX_FEATURES
    ]
);
#[cfg(not(target_arch = "riscv64"))]
codec!(
    Secp256k1,
    32,
    ec_secp256k1_compressed,
    vg_ec_secp256k1_compress_public_key,
    vg_ec_secp256k1_decompress_public_key,
    []
    [
        vg_ec_secp256k1_compress_public_key_umaal,
        vg_ec_secp256k1_decompress_public_key_umaal,
        VG_EC_SECP256K1_COMPRESS_PUBLIC_KEY_UMAAL_FEATURES,
        VG_EC_SECP256K1_DECOMPRESS_PUBLIC_KEY_UMAAL_FEATURES
    ]
);
#[cfg(not(target_arch = "riscv64"))]
codec!(
    BrainpoolP256r1,
    32,
    ec_brainpoolp256r1_compressed,
    vg_ec_brainpoolp256r1_compress_public_key,
    vg_ec_brainpoolp256r1_decompress_public_key,
    []
    [
        vg_ec_brainpoolp256r1_compress_public_key_umaal,
        vg_ec_brainpoolp256r1_decompress_public_key_umaal,
        VG_EC_BRAINPOOLP256R1_COMPRESS_PUBLIC_KEY_UMAAL_FEATURES,
        VG_EC_BRAINPOOLP256R1_DECOMPRESS_PUBLIC_KEY_UMAAL_FEATURES
    ]
);
#[cfg(not(target_arch = "riscv64"))]
codec!(
    BrainpoolP384r1,
    48,
    ec_brainpoolp384r1_compressed,
    vg_ec_brainpoolp384r1_compress_public_key,
    vg_ec_brainpoolp384r1_decompress_public_key,
    []
    [
        vg_ec_brainpoolp384r1_compress_public_key_umaal,
        vg_ec_brainpoolp384r1_decompress_public_key_umaal,
        VG_EC_BRAINPOOLP384R1_COMPRESS_PUBLIC_KEY_UMAAL_FEATURES,
        VG_EC_BRAINPOOLP384R1_DECOMPRESS_PUBLIC_KEY_UMAAL_FEATURES
    ]
);
#[cfg(not(target_arch = "riscv64"))]
codec!(
    BrainpoolP512r1,
    64,
    ec_brainpoolp512r1_compressed,
    vg_ec_brainpoolp512r1_compress_public_key,
    vg_ec_brainpoolp512r1_decompress_public_key,
    []
    [
        vg_ec_brainpoolp512r1_compress_public_key_umaal,
        vg_ec_brainpoolp512r1_decompress_public_key_umaal,
        VG_EC_BRAINPOOLP512R1_COMPRESS_PUBLIC_KEY_UMAAL_FEATURES,
        VG_EC_BRAINPOOLP512R1_DECOMPRESS_PUBLIC_KEY_UMAAL_FEATURES
    ]
);

#[cfg(test)]
mod tests {
    #[cfg(any(target_arch = "x86_64", target_arch = "arm"))]
    use super::*;
    use crate::ec::*;
    use crate::ecdh::PrivateKey;

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn backends() {
        let required = crate::arch::ec_p256_compressed::VG_EC_P256_COMPRESS_PUBLIC_KEY_ADX_FEATURES;
        for features in [
            Features(0),
            Features(verified_garbage_cpu::feature::BMI2),
            Features(verified_garbage_cpu::feature::ADX),
        ] {
            assert_eq!(Backend::select(features, required), Backend::Baseline);
        }
        assert_eq!(Backend::select(required, required), Backend::Fast);
    }

    #[cfg(target_arch = "arm")]
    #[test]
    fn backends() {
        let required =
            crate::arch::ec_p256_compressed::VG_EC_P256_COMPRESS_PUBLIC_KEY_UMAAL_FEATURES;
        assert_eq!(Backend::select(Features(0), required), Backend::Baseline);
        assert_eq!(Backend::select(required, required), Backend::Fast);
    }

    macro_rules! cases {
        ($name:ident, $curve:ident, $len:literal) => {
            #[test]
            fn $name() {
                for d in 1..=8 {
                    let mut private = [0; $len];
                    private[$len - 1] = d;
                    let public = PrivateKey::<$curve>::from_bytes(&private)
                        .public_key()
                        .unwrap();
                    let compressed = $curve::compress_public_key(&public).unwrap();
                    assert_eq!(compressed[0], 2 | (public[2 * $len] & 1));
                    assert_eq!(&compressed[1..], &public[1..1 + $len]);
                    assert_eq!($curve::decompress_public_key(&compressed), Some(public));
                    let mut opposite = compressed;
                    opposite[0] ^= 1;
                    let negated = $curve::decompress_public_key(&opposite).unwrap();
                    assert_ne!(negated, public);
                    assert_eq!($curve::compress_public_key(&negated), Some(opposite));
                    for tag in 0..=255 {
                        let mut q = compressed;
                        q[0] = tag;
                        assert_eq!(
                            $curve::decompress_public_key(&q).is_some(),
                            tag == 2 || tag == 3
                        );
                        let mut q = public;
                        q[0] = tag;
                        assert_eq!($curve::compress_public_key(&q).is_some(), tag == 4);
                    }
                    for i in 1..public.len() {
                        let mut q = public;
                        q[i] ^= 1;
                        assert_eq!($curve::compress_public_key(&q), None);
                    }
                }
                for tag in [0, 2, 3, 4, 6, 7] {
                    let mut q = [0xff; $len + 1];
                    q[0] = tag;
                    assert_eq!($curve::decompress_public_key(&q), None);
                    let mut q = [0; 2 * $len + 1];
                    q[0] = tag;
                    assert_eq!($curve::compress_public_key(&q), None);
                }
            }
        };
    }
    #[cfg(not(target_arch = "riscv64"))]
    cases!(p192, P192, 24);
    #[cfg(not(target_arch = "riscv64"))]
    cases!(p224, P224, 28);
    cases!(p256, P256, 32);
    cases!(p384, P384, 48);
    #[cfg(not(target_arch = "riscv64"))]
    cases!(p521, P521, 66);
    #[cfg(not(target_arch = "riscv64"))]
    cases!(secp256k1, Secp256k1, 32);
    #[cfg(not(target_arch = "riscv64"))]
    cases!(brainpoolp256r1, BrainpoolP256r1, 32);
    #[cfg(not(target_arch = "riscv64"))]
    cases!(brainpoolp384r1, BrainpoolP384r1, 48);
    #[cfg(not(target_arch = "riscv64"))]
    cases!(brainpoolp512r1, BrainpoolP512r1, 64);
}
