//! The hash functions as the verified functions take them: the hash
//! function as a table of functions of the interface `MdHash`, and MGF1's as
//! one of `Hash` (`crate::arch::fn_tables`): one `vg_rsa_pss_sign` and one
//! `vg_rsa_pss_verify_precomputed`, with each of the hash functions any of
//! them, rather than one for each pair of them.
//!
//! `md_table` and `table` choose a hash function's tables, as the backends
//! of the hash functions choose their implementations
//! (`crate::hashes::tables`); each architecture's file (`x86_64.rs`, …)
//! names its verified functions for each implementation of the RSA
//! operations (`pss_functions!`).

use super::Hash;
use crate::hashes::tables::TableHash;
use verified_garbage_cpu::Features;

/// The hash function with tables that `hash` is.
fn table_hash(hash: Hash) -> TableHash {
    match hash {
        Hash::Md5 => TableHash::Md5,
        Hash::Sha1 => TableHash::Sha1,
        Hash::Sha224 => TableHash::Sha224,
        Hash::Sha256 => TableHash::Sha256,
        Hash::Sha384 => TableHash::Sha384,
        Hash::Sha512 => TableHash::Sha512,
        Hash::Sha512_224 => TableHash::Sha512_224,
        Hash::Sha512_256 => TableHash::Sha512_256,
    }
}

/// The hash function `hash` as the verified functions take it, their
/// argument `hash`: the words of its table of `MdHash` for the
/// implementation that a CPU with the features `f` runs best.
pub(super) fn md_table(hash: Hash, f: Features) -> super::MdTable {
    table_hash(hash).md_hash_table(f)
}

/// MGF1's hash function `hash` as the verified functions take it, their
/// argument `mgf1`: the words of its table of `Hash`.
pub(super) fn table(hash: Hash, f: Features) -> super::Table {
    table_hash(hash).hash_table(f)
}

/// The verified functions: `functions`, which chooses, for a CPU with the
/// features `f`, the implementation of the RSA operations it runs best
/// (`crate::rsa::Backend`), and returns signing and verification calling
/// them; it does not compile if one needs a CPU feature that RSA's
/// `select` does not require to choose its implementation.
///
/// Each arm names, for one of RSA's backends on the architecture, signing
/// or verification, with the generated constants of the CPU features it
/// needs (none for the baseline ISA's).
macro_rules! pss_functions {
    (
        sign: {$($(#[$sattr:meta])* $sb:ident => $sign:path [$($sreq:path),*]),* $(,)?},
        verify: {$($(#[$vattr:meta])* $vb:ident => $verify:path [$($vreq:path),*]),* $(,)?} $(,)?
    ) => {
        // Each function needs no CPU feature that RSA's `select` does not
        // require to choose the implementation it is listed for.
        $(
            $(#[$sattr])*
            const _: () = assert!(
                crate::rsa::Backend::REQUIRES[crate::rsa::Backend::$sb as usize]
                    .contains(verified_garbage_cpu::Features::all(&[$($sreq),*])),
                "a signature needs a CPU feature its implementation is not chosen for"
            );
        )*
        $(
            $(#[$vattr])*
            const _: () = assert!(
                crate::rsa::Backend::REQUIRES[crate::rsa::Backend::$vb as usize]
                    .contains(verified_garbage_cpu::Features::all(&[$($vreq),*])),
                "a verification needs a CPU feature its implementation is not chosen for"
            );
        )*

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
    };
}

pub(super) use pss_functions;

#[cfg(test)]
mod tests {
    use super::{Hash, md_table, table};

    /// The tables of each hash function hold its digest length, the one the
    /// verified functions take the hash value's to be: a table of `MdHash`
    /// in its word 6, one of `Hash` in its word 4. (`crate::hashes::tables`
    /// checks the tables' CPU features and indices.)
    #[test]
    fn tables() {
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
        let f = crate::cpu::detected();
        for h in all {
            // SAFETY: the pointers point to the tables' words, of immutable
            // `'static` `repr(C)` values of 11 and 5 pointer-sized words.
            let (md, g) = unsafe { (*md_table(h, f), *table(h, f)) };
            assert_eq!(md[6], h.digest_len(), "{h:?}");
            assert_eq!(g[4], h.digest_len(), "{h:?}");
        }
    }
}
