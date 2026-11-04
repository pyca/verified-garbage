//! MGF1's hash function as the verified functions take it, a table of
//! functions of the interface `Hash` (`crate::arch::fn_tables`): for each
//! hash function `H`, one `vg_rsa_oaep_<H>_mgf1_encrypt_precomputed` and
//! one `vg_rsa_oaep_<H>_mgf1_decrypt`, with MGF1 over any of the hash
//! functions, rather than one for each pair.
//!
//! `mgf1` chooses the table of MGF1's hash function, as the backends of
//! the hash functions choose their implementations; each architecture's
//! file (`x86_64.rs`, …) names its tables (`mgf1_table`) and, in a module
//! for each `H`, its verified functions for each implementation of `H` and
//! of the RSA operation (`oaep_hash!`).

use super::arch::mgf1_table;
use crate::rsa_pkcs1_sig::Hash;
use verified_garbage_cpu::Features;

/// MGF1's hash function `hash` as the verified functions take it: the
/// words of its table for the implementation that a CPU with the features
/// `f` runs best, or `None` if MGF1 over `hash` is not supported.
pub(super) fn mgf1(hash: Hash, f: Features) -> Option<super::Mgf1> {
    mgf1_table(hash, f).map(|(t, _)| t.as_ptr())
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
/// and decryption for each of RSA's backends on the architecture, each
/// with the generated constants of the CPU features it needs (none for the
/// baseline ISA's).
macro_rules! oaep_hash {
    ($n:literal, $h:ident {
        $($(#[$hattr:meta])* $hv:ident => {
            encrypt: {$($(#[$eattr:meta])* $eb:ident => $enc:path [$($ereq:path),*]),* $(,)?},
            decrypt: {$($(#[$dattr:meta])* $db:ident => $dec:path [$($dreq:path),*]),* $(,)?} $(,)?
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
                $($(#[$hattr])* $h::$hv => (
                    match rsa {
                        $($(#[$eattr])* crate::rsa::Backend::$eb => $enc,)*
                    },
                    match rsa {
                        $($(#[$dattr])* crate::rsa::Backend::$db => $dec,)*
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
                        $($(#[$hattr])* $h::$hv => (
                            match rsa {
                                $($(#[$eattr])* crate::rsa::Backend::$eb =>
                                    verified_garbage_cpu::Features::all(&[$($ereq),*]),)*
                            },
                            match rsa {
                                $($(#[$dattr])* crate::rsa::Backend::$db =>
                                    verified_garbage_cpu::Features::all(&[$($dreq),*]),)*
                            },
                        ),)*
                    };
                    assert!(f.contains(encrypt) && f.contains(decrypt), "{bits:#b}");
                }
            }
        }
    };
}

pub(super) use oaep_hash;

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
