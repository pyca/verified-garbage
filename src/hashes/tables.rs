//! The hash functions as the verified functions that take one at run time
//! take it: a table of functions (`crate::arch::fn_tables`), of the
//! interface `Hash` (its streaming functions, as RSAES-OAEP's label and
//! MGF1 use it), `MdHash` (with its compression function, as RSASSA-PSS
//! uses it) or `Hmac` (HMAC over it, as deterministic ECDSA uses it).
//!
//! Each hash function's module names the tables of each of its
//! implementations (`streaming_hash!`'s `tables`), on each architecture; the
//! table for a CPU is that of the implementation the hash function runs on
//! it (its backend's `select`), so a table's functions are those the hash
//! function would call itself.

use crate::arch::fn_tables;
use crate::hashes::md5::Md5Backend;
use crate::hashes::sha1::Sha1Backend;
use crate::hashes::sha224::Sha224Backend;
use crate::hashes::sha256::Sha256Backend;
use crate::hashes::sha384::Sha384Backend;
use crate::hashes::sha512::Sha512Backend;
use crate::hashes::sha512_224::Sha512_224Backend;
use crate::hashes::sha512_256::Sha512_256Backend;
use verified_garbage_cpu::Features;

/// The tables of functions of one implementation of a hash function, which
/// need no CPU feature that its backend's `select` does not require to
/// choose it (`streaming_hash!` checks it when it compiles).
#[derive(Clone, Copy)]
pub(crate) struct Tables {
    /// Its table of `Hash`: `init`, `update` and `finalize`.
    #[cfg(feature = "alloc")]
    pub(crate) hash: &'static fn_tables::Hash,
    /// Its table of `MdHash`: those, its compression function and its
    /// digest of a state.
    #[cfg(feature = "alloc")]
    pub(crate) md_hash: &'static fn_tables::MdHash,
    /// Its table of `Hmac`: HMAC's `init`, the streaming `update` and HMAC's
    /// `finalize`, with its index, digest length and block size.
    pub(crate) hmac: &'static fn_tables::Hmac,
}

/// A hash function that has tables of functions (`VG.Spec.Mgf1.hashes`'
/// Merkle–Damgård ones).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TableHash {
    /// MD5.
    Md5,
    /// SHA-1.
    Sha1,
    /// SHA-224.
    Sha224,
    /// SHA-256.
    Sha256,
    /// SHA-384.
    Sha384,
    /// SHA-512.
    Sha512,
    /// SHA-512/224.
    Sha512_224,
    /// SHA-512/256.
    Sha512_256,
}

impl TableHash {
    /// The tables of the implementation that a CPU with the features `f`
    /// runs best.
    pub(crate) fn tables(self, f: Features) -> Tables {
        match self {
            Self::Md5 => Md5Backend::select(f).tables(),
            Self::Sha1 => Sha1Backend::select(f).tables(),
            Self::Sha224 => Sha224Backend::select(f).tables(),
            Self::Sha256 => Sha256Backend::select(f).tables(),
            Self::Sha384 => Sha384Backend::select(f).tables(),
            Self::Sha512 => Sha512Backend::select(f).tables(),
            Self::Sha512_224 => Sha512_224Backend::select(f).tables(),
            Self::Sha512_256 => Sha512_256Backend::select(f).tables(),
        }
    }

    /// Its table of `Hash`, as the verified functions take it: the words of
    /// the table of the implementation that a CPU with the features `f`
    /// runs best.
    #[cfg(feature = "alloc")]
    pub(crate) fn hash_table(self, f: Features) -> *const [usize; 5] {
        self.tables(f).hash.as_ptr()
    }

    /// Its table of `MdHash`, as the verified functions take it.
    #[cfg(feature = "alloc")]
    pub(crate) fn md_hash_table(self, f: Features) -> *const [usize; 11] {
        self.tables(f).md_hash.as_ptr()
    }

    /// Its table of `Hmac`, as the verified functions take it.
    pub(crate) fn hmac_table(self, f: Features) -> *const [usize; 6] {
        self.tables(f).hmac.as_ptr()
    }
}

#[cfg(test)]
mod tests {
    use super::{
        Md5Backend, Sha1Backend, Sha224Backend, Sha256Backend, Sha384Backend, Sha512_224Backend,
        Sha512_256Backend, Sha512Backend, TableHash,
    };

    /// A table of `Hash` holds the hash function's index and digest length
    /// (its words 3 and 4), as its table of `MdHash` does (words 5 and 6),
    /// and its table of `Hmac` holds them and HMAC's block size (words 3, 4
    /// and 5); and the indices are those of `VG.Spec.Mgf1.hashes`, in this
    /// order: for the implementations a CPU with exactly the features any
    /// implementation's `select` requires runs, so for each of them.
    #[test]
    fn table_words() {
        let all = [
            (TableHash::Md5, 16, 64),
            (TableHash::Sha1, 20, 64),
            (TableHash::Sha224, 28, 64),
            (TableHash::Sha256, 32, 64),
            (TableHash::Sha384, 48, 128),
            (TableHash::Sha512, 64, 128),
            (TableHash::Sha512_224, 28, 128),
            (TableHash::Sha512_256, 32, 128),
        ];
        let sets = [
            Md5Backend::REQUIRES,
            Sha1Backend::REQUIRES,
            Sha224Backend::REQUIRES,
            Sha256Backend::REQUIRES,
            Sha384Backend::REQUIRES,
            Sha512Backend::REQUIRES,
            Sha512_224Backend::REQUIRES,
            Sha512_256Backend::REQUIRES,
        ];
        for &f in sets.into_iter().flatten() {
            for (i, (h, len, block)) in all.into_iter().enumerate() {
                #[cfg(feature = "alloc")]
                {
                    // SAFETY: `as_ptr` points to the tables' words, of
                    // immutable `'static` `repr(C)` values of 5 and 11
                    // pointer-sized words.
                    let (g, md) = unsafe { (*h.hash_table(f), *h.md_hash_table(f)) };
                    assert_eq!((g[3], g[4]), (i, len), "{h:?} {f:?}");
                    assert_eq!((md[5], md[6]), (i, len), "{h:?} {f:?}");
                }
                // SAFETY: `as_ptr` points to the table's words, of an
                // immutable `'static` `repr(C)` value of 6 pointer-sized
                // words.
                let m = unsafe { *h.hmac_table(f) };
                assert_eq!((m[3], m[4], m[5]), (i, len, block), "{h:?} {f:?}");
            }
        }
    }
}
