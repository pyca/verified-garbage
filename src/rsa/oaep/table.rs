//! The hash functions as the tables of functions that RSAES-OAEP's verified
//! functions take.

use crate::hashes::tables::TableHash;
use crate::rsa::pkcs1_sig::Hash;
use verified_garbage_cpu::Features;

/// The hash function `hash` as the verified functions take it: the words of
/// its table of `Hash` for the implementation that a CPU with the features
/// `f` runs best, or `None` if `hash` is not supported (MD5, which RSAES-OAEP
/// does not use, and SHA-3's, which have no table).
pub(super) fn table(hash: Hash, f: Features) -> Option<super::Table> {
    let h = match hash {
        Hash::Sha1 => TableHash::Sha1,
        Hash::Sha224 => TableHash::Sha224,
        Hash::Sha256 => TableHash::Sha256,
        Hash::Sha384 => TableHash::Sha384,
        Hash::Sha512 => TableHash::Sha512,
        Hash::Sha512_224 => TableHash::Sha512_224,
        Hash::Sha512_256 => TableHash::Sha512_256,
        _ => return None,
    };
    Some(h.hash_table(f))
}

/// The verified functions: `functions`, which chooses, for a CPU with the
/// features `f`, the implementation of the RSA operations it runs best
/// (`crate::rsa::Backend`), and returns encryption and decryption calling
/// them; it does not compile if one needs a CPU feature that RSA's
/// `select` does not require to choose its implementation.
///
/// Each arm names, for one of RSA's backends on the architecture, encryption
/// or decryption, with the generated constants of the CPU features it needs
/// (none for the baseline ISA's).
macro_rules! oaep_functions {
    (
        encrypt: {$($(#[$eattr:meta])* $eb:ident => $enc:path [$($ereq:ident),*]),* $(,)?},
        decrypt: {$($(#[$dattr:meta])* $db:ident => $dec:path [$($dreq:ident),*]),* $(,)?} $(,)?
    ) => {
        // Each function needs no CPU feature that RSA's `select` does not
        // require to choose the implementation it is listed for.
        $(
            $(#[$eattr])*
            const _: () = assert!(
                crate::rsa::Backend::REQUIRES[crate::rsa::Backend::$eb as usize]
                    .contains(verified_garbage_cpu::Features::all(&[$($ereq),*])),
                "an encryption needs a CPU feature its implementation is not chosen for"
            );
        )*
        $(
            $(#[$dattr])*
            const _: () = assert!(
                crate::rsa::Backend::REQUIRES[crate::rsa::Backend::$db as usize]
                    .contains(verified_garbage_cpu::Features::all(&[$($dreq),*])),
                "a decryption needs a CPU feature its implementation is not chosen for"
            );
        )*

        /// The functions, `(encrypt, decrypt)`, for the implementation that a
        /// CPU with the features `f` runs best.
        pub(in crate::rsa::oaep) fn functions(
            f: verified_garbage_cpu::Features,
        ) -> (crate::rsa::oaep::EncryptFn, crate::rsa::oaep::DecryptFn) {
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
    };
}

pub(super) use oaep_functions;

#[cfg(test)]
mod tests {
    use super::{Hash, table};

    /// Every hash function but MD5 and SHA-3's has a table, whose word 4 is
    /// the hash function's digest length, which encryption takes as the
    /// seed's. (`streaming_hash!` checks the tables' CPU features when it
    /// compiles.)
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
            Hash::Sha3_224,
            Hash::Sha3_256,
            Hash::Sha3_384,
            Hash::Sha3_512,
        ];
        let f = crate::cpu::detected();
        let mut n = 0;
        for h in all {
            if let Some(t) = table(h, f) {
                // SAFETY: `t` points to a table's five words, of an
                // immutable `'static` `repr(C)` value.
                assert_eq!(unsafe { (*t)[4] }, h.digest_len(), "{h:?}");
                n += 1;
            }
        }
        assert_eq!(n, 7);
    }
}
