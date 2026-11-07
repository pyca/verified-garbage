//! SEC 1 point compression and decompression, with validation.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

/// The compression and decompression of the curve `$curve`, whose
/// coordinates are `$len` bytes, by the dispatchers `$compress` and
/// `$decompress` of `crate::arch::dispatch::$module`.
macro_rules! codec {
    ($curve:ident, $len:literal, $module:ident, $compress:ident, $decompress:ident) => {
        impl super::$curve {
            /// Validates and compresses `04 || x || y` to SEC 1 `02/03 || x`.
            ///
            /// Returns `None` for an invalid encoding or curve point.
            /// Infinity and hybrid encodings are rejected.
            pub fn compress_public_key(public: &[u8; 2 * $len + 1]) -> Option<[u8; $len + 1]> {
                use crate::arch::dispatch::$module::$compress;
                let dit = crate::dit::public(crate::dit::Why::PublicKey);
                let mut out = [0; $len + 1];
                let mut ws = [0u64; 1024];
                // SAFETY: all three arrays have the contract's lengths and
                // occupy separate Rust objects. Their ranges cannot wrap or
                // overlap the return address. The dispatcher calls only an
                // implementation the CPU has the features of.
                let ok = unsafe { $compress(dit, &mut out, public, &mut ws) };
                (ok == 1).then_some(out)
            }

            /// Validates and decompresses SEC 1 `02/03 || x` to `04 || x || y`.
            ///
            /// Returns `None` if no finite curve point has the encoded x and
            /// parity. Infinity and hybrid encodings are rejected.
            /// Timing may depend on these public input bytes.
            pub fn decompress_public_key(public: &[u8; $len + 1]) -> Option<[u8; 2 * $len + 1]> {
                use crate::arch::dispatch::$module::$decompress;
                let dit = crate::dit::public(crate::dit::Why::PublicKey);
                let mut out = [0; 2 * $len + 1];
                let mut ws = [0u64; 1024];
                // SAFETY: all three arrays have the contract's lengths and
                // occupy separate Rust objects. Their ranges cannot wrap or
                // overlap the return address. The dispatcher calls only an
                // implementation the CPU has the features of.
                let ok = unsafe { $decompress(dit, &mut out, public, &mut ws) };
                (ok == 1).then_some(out)
            }
        }
    };
}

codec!(
    P192,
    24,
    ec_p192_compressed,
    vg_ec_p192_compress_public_key_auto,
    vg_ec_p192_decompress_public_key_auto
);
codec!(
    P224,
    28,
    ec_p224_compressed,
    vg_ec_p224_compress_public_key_auto,
    vg_ec_p224_decompress_public_key_auto
);
codec!(
    P256,
    32,
    ec_p256_compressed,
    vg_ec_p256_compress_public_key_auto,
    vg_ec_p256_decompress_public_key_auto
);
codec!(
    P384,
    48,
    ec_p384_compressed,
    vg_ec_p384_compress_public_key_auto,
    vg_ec_p384_decompress_public_key_auto
);
codec!(
    P521,
    66,
    ec_p521_compressed,
    vg_ec_p521_compress_public_key_auto,
    vg_ec_p521_decompress_public_key_auto
);
codec!(
    Secp256k1,
    32,
    ec_secp256k1_compressed,
    vg_ec_secp256k1_compress_public_key_auto,
    vg_ec_secp256k1_decompress_public_key_auto
);
codec!(
    BrainpoolP256r1,
    32,
    ec_brainpoolp256r1_compressed,
    vg_ec_brainpoolp256r1_compress_public_key_auto,
    vg_ec_brainpoolp256r1_decompress_public_key_auto
);
codec!(
    BrainpoolP384r1,
    48,
    ec_brainpoolp384r1_compressed,
    vg_ec_brainpoolp384r1_compress_public_key_auto,
    vg_ec_brainpoolp384r1_decompress_public_key_auto
);
codec!(
    BrainpoolP512r1,
    64,
    ec_brainpoolp512r1_compressed,
    vg_ec_brainpoolp512r1_compress_public_key_auto,
    vg_ec_brainpoolp512r1_decompress_public_key_auto
);

#[cfg(test)]
mod tests {
    #[cfg(not(target_arch = "riscv64"))]
    use crate::ec::P521;
    use crate::ec::PrivateKey;
    use crate::ec::{
        BrainpoolP256r1, BrainpoolP384r1, BrainpoolP512r1, P192, P224, P256, P384, Secp256k1,
    };

    macro_rules! cases {
        ($name:ident, $curve:ident, $len:literal) => {
            #[test]
            fn $name() {
                for d in 1..=8 {
                    let mut private = [0; $len];
                    private[$len - 1] = d;
                    let public = *PrivateKey::<$curve>::from_bytes(&private)
                        .public_key()
                        .unwrap()
                        .as_bytes();
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
    cases!(p192, P192, 24);
    cases!(p224, P224, 28);
    cases!(p256, P256, 32);
    cases!(p384, P384, 48);
    #[cfg(not(target_arch = "riscv64"))]
    cases!(p521, P521, 66);
    cases!(secp256k1, Secp256k1, 32);
    cases!(brainpoolp256r1, BrainpoolP256r1, 32);
    cases!(brainpoolp384r1, BrainpoolP384r1, 48);
    cases!(brainpoolp512r1, BrainpoolP512r1, 64);
}
