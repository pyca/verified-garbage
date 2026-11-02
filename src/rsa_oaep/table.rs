//! RSAES-OAEP on x86-64, where the verified functions take MGF1's hash
//! function as a table of functions of the interface `Hash`
//! (`crate::arch::fn_tables`): for each hash function `H`, one
//! `vg_rsa_oaep_<H>_encrypt_precomputed` and one `vg_rsa_oaep_<H>_decrypt`,
//! with MGF1 over any of the hash functions, rather than one for each pair.
//!
//! `mgf1` chooses the table of MGF1's hash function, as the backends of
//! the hash functions choose their implementations; each `H` has a file,
//! `<H>.rs`, naming its verified functions for each implementation of `H`
//! and of the RSA operation (`oaep_hash!`).

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

mod sha1;
mod sha224;
mod sha256;
mod sha384;
mod sha512;
mod sha512_224;
mod sha512_256;

use crate::arch::fn_tables::{self, *};
use crate::hashes::sha1::Sha1Backend;
use crate::hashes::sha224::Sha224Backend;
use crate::hashes::sha256::Sha256Backend;
use crate::hashes::sha384::Sha384Backend;
use crate::hashes::sha512::Sha512Backend;
use crate::hashes::sha512_224::Sha512_224Backend;
use crate::hashes::sha512_256::Sha512_256Backend;
use crate::rsa_pkcs1_sig::Hash;
use verified_garbage_cpu::Features;

/// The table of MGF1's hash function `hash` for the implementation that a
/// CPU with the features `f` runs best, with the features its functions
/// need, or `None` if MGF1 over `hash` is not supported.
fn mgf1_table(hash: Hash, f: Features) -> Option<(&'static fn_tables::Hash, Features)> {
    let none = Features(0);
    Some(match hash {
        Hash::Sha1 => match Sha1Backend::select(f) {
            Sha1Backend::Scalar => (&VG_HASH_SHA1, none),
            Sha1Backend::ShaNi => (&VG_HASH_SHA1_SHANI, VG_HASH_SHA1_SHANI_FEATURES),
        },
        Hash::Sha224 => match Sha224Backend::select(f) {
            Sha224Backend::Scalar => (&VG_HASH_SHA224, none),
            Sha224Backend::ShaNi => (&VG_HASH_SHA224_SHANI, VG_HASH_SHA224_SHANI_FEATURES),
            Sha224Backend::Avx2 => (&VG_HASH_SHA224_AVX2, VG_HASH_SHA224_AVX2_FEATURES),
        },
        Hash::Sha256 => match Sha256Backend::select(f) {
            Sha256Backend::Scalar => (&VG_HASH_SHA256, none),
            Sha256Backend::ShaNi => (&VG_HASH_SHA256_SHANI, VG_HASH_SHA256_SHANI_FEATURES),
            Sha256Backend::Avx2 => (&VG_HASH_SHA256_AVX2, VG_HASH_SHA256_AVX2_FEATURES),
        },
        Hash::Sha384 => match Sha384Backend::select(f) {
            Sha384Backend::Scalar => (&VG_HASH_SHA384, none),
            Sha384Backend::ShaNi => (&VG_HASH_SHA384_SHANI, VG_HASH_SHA384_SHANI_FEATURES),
            Sha384Backend::Avx2 => (&VG_HASH_SHA384_AVX2, VG_HASH_SHA384_AVX2_FEATURES),
        },
        Hash::Sha512 => match Sha512Backend::select(f) {
            Sha512Backend::Scalar => (&VG_HASH_SHA512, none),
            Sha512Backend::ShaNi => (&VG_HASH_SHA512_SHANI, VG_HASH_SHA512_SHANI_FEATURES),
            Sha512Backend::Avx2 => (&VG_HASH_SHA512_AVX2, VG_HASH_SHA512_AVX2_FEATURES),
        },
        Hash::Sha512_224 => match Sha512_224Backend::select(f) {
            Sha512_224Backend::Scalar => (&VG_HASH_SHA512_224, none),
            Sha512_224Backend::ShaNi => (&VG_HASH_SHA512_224_SHANI, VG_HASH_SHA512_224_SHANI_FEATURES),
            Sha512_224Backend::Avx2 => (&VG_HASH_SHA512_224_AVX2, VG_HASH_SHA512_224_AVX2_FEATURES),
        },
        Hash::Sha512_256 => match Sha512_256Backend::select(f) {
            Sha512_256Backend::Scalar => (&VG_HASH_SHA512_256, none),
            Sha512_256Backend::ShaNi => (&VG_HASH_SHA512_256_SHANI, VG_HASH_SHA512_256_SHANI_FEATURES),
            Sha512_256Backend::Avx2 => (&VG_HASH_SHA512_256_AVX2, VG_HASH_SHA512_256_AVX2_FEATURES),
        },
        _ => return None,
    })
}

/// MGF1's hash function `hash` as the verified functions take it: the
/// words of its table for the implementation that a CPU with the features
/// `f` runs best, or `None` if MGF1 over `hash` is not supported.
pub(super) fn mgf1(hash: Hash, f: Features) -> Option<super::Mgf1> {
    mgf1_table(hash, f).map(|(t, _)| t.words())
}

/// The verified functions of one hash function `H`, of `$n`-byte values:
/// `functions`, which chooses, for a CPU with the features `f`, the
/// implementations of its compression function it runs best (the variants
/// of its streaming backend, `$h`) and of the RSA operations
/// (`crate::rsa::Backend`), and returns encryption and decryption calling
/// them; and a test that each needs no CPU feature that was not required to
/// choose it.
///
/// Each arm names, for one implementation of the hash function, encryption
/// and decryption for each of RSA's backends, each with the generated
/// constants of the CPU features it needs (none for the baseline ISA's).
macro_rules! oaep_hash {
    ($n:literal, $h:ident {
        $($hv:ident => {
            encrypt: $enc:path [$($ereq:path),*],
            decrypt: $dec:path [$($dreq:path),*],
            encrypt_adx: $enc_adx:path [$($eareq:path),*],
            encrypt_ifma: $enc_ifma:path [$($eireq:path),*],
            decrypt_adx: $dec_adx:path [$($dareq:path),*],
            decrypt_ifma: $dec_ifma:path [$($direq:path),*] $(,)?
        }),* $(,)?
    }) => {
        /// The length of the hash function's values.
        const N: usize = $n;

        /// The functions, `(encrypt, decrypt)`, for the implementations
        /// that a CPU with the features `f` runs best.
        pub(in crate::rsa_oaep) fn functions(
            f: verified_garbage_cpu::Features,
        ) -> (crate::rsa_oaep::EncryptFn<N>, crate::rsa_oaep::DecryptFn) {
            let rsa = crate::rsa::Backend::select(f);
            match $h::select(f) {
                $($h::$hv => (
                    match rsa {
                        crate::rsa::Backend::Baseline => $enc,
                        crate::rsa::Backend::Adx => $enc_adx,
                        crate::rsa::Backend::Ifma => $enc_ifma,
                    },
                    match rsa {
                        crate::rsa::Backend::Baseline => $dec,
                        crate::rsa::Backend::Adx => $dec_adx,
                        crate::rsa::Backend::Ifma => $dec_ifma,
                    },
                ),)*
            }
        }

        #[cfg(test)]
        mod tests {
            use super::*;

            /// Each function needs no CPU feature that the implementations
            /// it calls were not chosen for: on every set of features.
            #[test]
            fn backend_features() {
                for bits in 0..1u32 << crate::cpu::NAMES.len() {
                    let f = verified_garbage_cpu::Features(bits);
                    let rsa = crate::rsa::Backend::select(f);
                    let (encrypt, decrypt) = match $h::select(f) {
                        $($h::$hv => (
                            match rsa {
                                crate::rsa::Backend::Baseline => verified_garbage_cpu::Features::all(&[$($ereq),*]),
                                crate::rsa::Backend::Adx => verified_garbage_cpu::Features::all(&[$($eareq),*]),
                                crate::rsa::Backend::Ifma => verified_garbage_cpu::Features::all(&[$($eireq),*]),
                            },
                            match rsa {
                                crate::rsa::Backend::Baseline => verified_garbage_cpu::Features::all(&[$($dreq),*]),
                                crate::rsa::Backend::Adx => verified_garbage_cpu::Features::all(&[$($dareq),*]),
                                crate::rsa::Backend::Ifma => verified_garbage_cpu::Features::all(&[$($direq),*]),
                            },
                        ),)*
                    };
                    assert!(f.contains(encrypt) && f.contains(decrypt), "{bits:#b}");
                }
            }
        }
    };
}

use oaep_hash;

#[cfg(test)]
mod tests {
    use super::*;

    /// Each table's functions need no CPU feature that was not required to
    /// choose it, on every set of features, and MGF1 is over every hash
    /// function but MD5 and SHA-3's.
    #[test]
    fn table_features() {
        let all = [
            Hash::Md5,
            Hash::Sha1,
            Hash::Sha224,
            Hash::Sha256,
            Hash::Sha384,
            Hash::Sha512,
            Hash::Sha512_224,
            Hash::Sha512_256,
            Hash::Sha3_224,
            Hash::Sha3_256,
            Hash::Sha3_384,
            Hash::Sha3_512,
        ];
        for bits in 0..1u32 << crate::cpu::NAMES.len() {
            let f = Features(bits);
            let mut n = 0;
            for h in all {
                if let Some((_, need)) = mgf1_table(h, f) {
                    assert!(f.contains(need), "{h:?} {bits:#b}");
                    n += 1;
                }
                assert_eq!(mgf1(h, f).is_some(), mgf1_table(h, f).is_some());
            }
            assert_eq!(n, 7);
        }
    }
}
