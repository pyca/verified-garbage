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

/// The tables of functions of one implementation of a hash function, each
/// with the CPU features its functions need.
#[derive(Clone, Copy)]
pub(crate) struct Tables {
    /// Its table of `Hash`: `init`, `update` and `finalize`.
    #[cfg(feature = "alloc")]
    pub(crate) hash: (&'static fn_tables::Hash, Features),
    /// Its table of `MdHash`: those, its compression function and its
    /// digest of a state.
    #[cfg(feature = "alloc")]
    pub(crate) md_hash: (&'static fn_tables::MdHash, Features),
    /// Its table of `Hmac`: HMAC's `init`, the streaming `update` and HMAC's
    /// `finalize`, with its index, digest length and block size.
    pub(crate) hmac: (&'static fn_tables::Hmac, Features),
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
        self.tables(f).hash.0.as_ptr()
    }

    /// Its table of `MdHash`, as the verified functions take it.
    #[cfg(feature = "alloc")]
    pub(crate) fn md_hash_table(self, f: Features) -> *const [usize; 11] {
        self.tables(f).md_hash.0.as_ptr()
    }

    /// Its table of `Hmac`, as the verified functions take it.
    pub(crate) fn hmac_table(self, f: Features) -> *const [usize; 6] {
        self.tables(f).hmac.0.as_ptr()
    }
}

#[cfg(test)]
mod tests {
    use super::TableHash;

    /// Each table's functions need no CPU feature that was not required to
    /// choose it, on every set of features; a table of `Hash` holds the hash
    /// function's index and digest length (its words 3 and 4), as its table
    /// of `MdHash` does (words 5 and 6), and its table of `Hmac` holds them
    /// and HMAC's block size (words 3, 4 and 5); and the indices are those of
    /// `VG.Spec.Mgf1.hashes`, in this order.
    #[test]
    fn table_features() {
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
        for f in crate::cpu::feature_sets() {
            let bits = f.0;
            for (i, (h, len, block)) in all.into_iter().enumerate() {
                let t = h.tables(f);
                #[cfg(feature = "alloc")]
                {
                    assert!(f.contains(t.hash.1), "{h:?} {bits:#b}");
                    assert!(f.contains(t.md_hash.1), "{h:?} {bits:#b}");
                    // SAFETY: `as_ptr` points to the tables' words, of
                    // immutable `'static` `repr(C)` values of 5 and 11
                    // pointer-sized words.
                    let (g, md) = unsafe { (*h.hash_table(f), *h.md_hash_table(f)) };
                    assert_eq!((g[3], g[4]), (i, len), "{h:?}");
                    assert_eq!((md[5], md[6]), (i, len), "{h:?}");
                }
                assert!(f.contains(t.hmac.1), "{h:?} {bits:#b}");
                // SAFETY: `as_ptr` points to the table's words, of an
                // immutable `'static` `repr(C)` value of 6 pointer-sized
                // words.
                let m = unsafe { *h.hmac_table(f) };
                assert_eq!((m[3], m[4], m[5]), (i, len, block), "{h:?}");
            }
        }
    }
}
