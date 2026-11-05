//! The hash functions as the verified functions take them: the hash
//! function as a table of functions of the interface `MdHash`, and MGF1's as
//! one of `Hash` (`crate::arch::fn_tables`): one `vg_rsa_pss_sign` and one
//! `vg_rsa_pss_verify_precomputed`, with each of the hash functions any of
//! them, rather than one for each pair of them.
//!
//! `md_table` and `table` choose a hash function's tables, as the backends
//! of the hash functions choose their implementations; each architecture's
//! file (`x86_64.rs`, …) names its tables (`md_hash_table`, `hash_table`)
//! and its verified functions for each implementation of the RSA operations
//! (`pss_functions!`).

use super::Hash;
use super::arch::{hash_table, md_hash_table};
use verified_garbage_cpu::Features;

/// The hash function `hash` as the verified functions take it, their
/// argument `hash`: the words of its table of `MdHash` for the
/// implementation that a CPU with the features `f` runs best.
pub(super) fn md_table(hash: Hash, f: Features) -> super::MdTable {
    md_hash_table(hash, f).0.as_ptr()
}

/// MGF1's hash function `hash` as the verified functions take it, their
/// argument `mgf1`: the words of its table of `Hash`.
pub(super) fn table(hash: Hash, f: Features) -> super::Table {
    hash_table(hash, f).0.as_ptr()
}

/// The verified functions: `functions`, which chooses, for a CPU with the
/// features `f`, the implementation of the RSA operations it runs best
/// (`crate::rsa::Backend`), and returns signing and verification calling
/// them; and a test that each needs no CPU feature that was not required to
/// choose it.
///
/// Each arm names, for one of RSA's backends on the architecture, signing
/// or verification, with the generated constants of the CPU features it
/// needs (none for the baseline ISA's).
macro_rules! pss_functions {
    (
        sign: {$($(#[$sattr:meta])* $sb:ident => $sign:path [$($sreq:path),*]),* $(,)?},
        verify: {$($(#[$vattr:meta])* $vb:ident => $verify:path [$($vreq:path),*]),* $(,)?} $(,)?
    ) => {
        /// The functions, `(sign, verify)`, for the implementation that a
        /// CPU with the features `f` runs best.
        pub(in crate::rsa_pss) fn functions(
            f: verified_garbage_cpu::Features,
        ) -> (crate::rsa_pss::SignFn, crate::rsa_pss::VerifyFn) {
            let rsa = crate::rsa::Backend::select(f);
            (
                match rsa {
                    $($(#[$sattr])* crate::rsa::Backend::$sb => $sign,)*
                },
                match rsa {
                    $($(#[$vattr])* crate::rsa::Backend::$vb => $verify,)*
                },
            )
        }

        #[cfg(test)]
        mod function_tests {
            /// Each function needs no CPU feature that the implementations
            /// it calls were not chosen for: on every set of features.
            #[test]
            fn backend_features() {
                for bits in 0..1u32 << crate::cpu::NAMES.len() {
                    let f = verified_garbage_cpu::Features(bits);
                    let rsa = crate::rsa::Backend::select(f);
                    let sign = match rsa {
                        $($(#[$sattr])* crate::rsa::Backend::$sb =>
                            verified_garbage_cpu::Features::all(&[$($sreq),*]),)*
                    };
                    let verify = match rsa {
                        $($(#[$vattr])* crate::rsa::Backend::$vb =>
                            verified_garbage_cpu::Features::all(&[$($vreq),*]),)*
                    };
                    assert!(f.contains(sign) && f.contains(verify), "{bits:#b}");
                }
            }
        }
    };
}

pub(super) use pss_functions;

#[cfg(test)]
mod tests {
    use super::{Features, Hash, hash_table, md_hash_table, md_table, table};

    /// Each table's functions need no CPU feature that was not required to
    /// choose it, on every set of features; a table of `MdHash` holds the
    /// hash function's index and digest length (its words 5 and 6), as its
    /// table of `Hash` does (words 3 and 4), the digest length the verified
    /// functions take the hash value's to be.
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
        ];
        for bits in 0..1u32 << crate::cpu::NAMES.len() {
            let f = Features(bits);
            for h in all {
                let (t, need) = md_hash_table(h, f);
                assert!(f.contains(need), "{h:?} {bits:#b}");
                let (g, gneed) = hash_table(h, f);
                assert!(f.contains(gneed), "{h:?} {bits:#b}");
                // SAFETY: `as_ptr` points to the tables' words, of immutable
                // `'static` `repr(C)` values of 11 and 5 pointer-sized words.
                let (words, gwords) = unsafe { (*t.as_ptr(), *g.as_ptr()) };
                assert_eq!(words[6], h.digest_len(), "{h:?}");
                assert_eq!(gwords[4], h.digest_len(), "{h:?}");
                assert_eq!(words[5], gwords[3], "{h:?}");
                assert_eq!(md_table(h, f), t.as_ptr());
                assert_eq!(table(h, f), g.as_ptr());
            }
        }
    }
}
