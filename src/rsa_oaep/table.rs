//! The hash functions as the verified functions take them, tables of
//! functions of the interface `Hash` (`crate::arch::fn_tables`): one
//! `vg_rsa_oaep_encrypt_precomputed` and one `vg_rsa_oaep_decrypt`, with
//! the label's hash function and MGF1's each any of the hash functions,
//! rather than one for each hash function or pair of them.
//!
//! `table` chooses a hash function's table, as the backends of the hash
//! functions choose their implementations; each architecture's file
//! (`x86_64.rs`, …) names its tables (`hash_table`) and its verified
//! functions for each implementation of the RSA operations
//! (`oaep_functions!`).

use super::arch::hash_table;
use crate::rsa_pkcs1_sig::Hash;
use verified_garbage_cpu::Features;

/// The hash function `hash` as the verified functions take it: the words of
/// its table for the implementation that a CPU with the features `f` runs
/// best, or `None` if `hash` is not supported.
pub(super) fn table(hash: Hash, f: Features) -> Option<super::Table> {
    hash_table(hash, f).map(|(t, _)| t.as_ptr())
}

/// The verified functions: `functions`, which chooses, for a CPU with the
/// features `f`, the implementation of the RSA operations it runs best
/// (`crate::rsa::Backend`), and returns encryption and decryption calling
/// them; and a test that each needs no CPU feature that was not required to
/// choose it.
///
/// Each arm names, for one of RSA's backends on the architecture, encryption
/// or decryption, with the generated constants of the CPU features it needs
/// (none for the baseline ISA's).
macro_rules! oaep_functions {
    (
        encrypt: {$($(#[$eattr:meta])* $eb:ident => $enc:path [$($ereq:path),*]),* $(,)?},
        decrypt: {$($(#[$dattr:meta])* $db:ident => $dec:path [$($dreq:path),*]),* $(,)?} $(,)?
    ) => {
        /// The functions, `(encrypt, decrypt)`, for the implementation that a
        /// CPU with the features `f` runs best.
        pub(in crate::rsa_oaep) fn functions(
            f: verified_garbage_cpu::Features,
        ) -> (crate::rsa_oaep::EncryptFn, crate::rsa_oaep::DecryptFn) {
            let rsa = crate::rsa::Backend::select(f);
            (
                match rsa {
                    $($(#[$eattr])* crate::rsa::Backend::$eb => $enc,)*
                },
                match rsa {
                    $($(#[$dattr])* crate::rsa::Backend::$db => $dec,)*
                },
            )
        }

        #[cfg(test)]
        mod function_tests {
            #[allow(unused_imports)]
            use super::*;

            /// Each function needs no CPU feature that the implementations
            /// it calls were not chosen for: on every set of features.
            #[test]
            fn backend_features() {
                for bits in 0..1u32 << crate::cpu::NAMES.len() {
                    let f = verified_garbage_cpu::Features(bits);
                    let rsa = crate::rsa::Backend::select(f);
                    let encrypt = match rsa {
                        $($(#[$eattr])* crate::rsa::Backend::$eb =>
                            verified_garbage_cpu::Features::all(&[$($ereq),*]),)*
                    };
                    let decrypt = match rsa {
                        $($(#[$dattr])* crate::rsa::Backend::$db =>
                            verified_garbage_cpu::Features::all(&[$($dreq),*]),)*
                    };
                    assert!(f.contains(encrypt) && f.contains(decrypt), "{bits:#b}");
                }
            }
        }
    };
}

pub(super) use oaep_functions;

#[cfg(test)]
mod tests {
    use super::*;

    /// Each table's functions need no CPU feature that was not required to
    /// choose it, on every set of features; its word 4 is the hash
    /// function's digest length, which encryption takes as the seed's; and
    /// every hash function but MD5 and SHA-3's has one.
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
                if let Some((t, need)) = hash_table(h, f) {
                    assert!(f.contains(need), "{h:?} {bits:#b}");
                    // SAFETY: `as_ptr` points to the table's five words, of
                    // an immutable `'static` `repr(C)` value of five
                    // pointer-sized words.
                    let len = unsafe { (*t.as_ptr())[4] };
                    assert_eq!(len, h.digest_len(), "{h:?}");
                    n += 1;
                }
                assert_eq!(table(h, f).is_some(), hash_table(h, f).is_some());
            }
            assert_eq!(n, 7);
        }
    }
}
