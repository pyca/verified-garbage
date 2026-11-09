//! The hash functions as tables of functions, for the verified functions that
//! take a hash function at run time (RSAES-OAEP, RSASSA-PSS, deterministic
//! ECDSA).

use crate::arch::dispatch::fn_tables as auto;
use crate::arch::fn_tables;

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
    /// Its table of `Hash`, as the verified functions take it: the words of
    /// the best table this CPU runs (its dispatcher's,
    /// `crate::arch::dispatch::fn_tables`).
    #[cfg(feature = "alloc")]
    pub(crate) fn hash_table(self) -> *const [usize; 5] {
        let t: &'static fn_tables::Hash = match self {
            Self::Md5 => auto::vg_hash_md5_auto(),
            Self::Sha1 => auto::vg_hash_sha1_auto(),
            Self::Sha224 => auto::vg_hash_sha224_auto(),
            Self::Sha256 => auto::vg_hash_sha256_auto(),
            Self::Sha384 => auto::vg_hash_sha384_auto(),
            Self::Sha512 => auto::vg_hash_sha512_auto(),
            Self::Sha512_224 => auto::vg_hash_sha512_224_auto(),
            Self::Sha512_256 => auto::vg_hash_sha512_256_auto(),
        };
        t.as_ptr()
    }

    /// Its table of `MdHash`, as the verified functions take it.
    #[cfg(feature = "alloc")]
    pub(crate) fn md_hash_table(self) -> *const [usize; 11] {
        let t: &'static fn_tables::MdHash = match self {
            Self::Md5 => auto::vg_md_hash_md5_auto(),
            Self::Sha1 => auto::vg_md_hash_sha1_auto(),
            Self::Sha224 => auto::vg_md_hash_sha224_auto(),
            Self::Sha256 => auto::vg_md_hash_sha256_auto(),
            Self::Sha384 => auto::vg_md_hash_sha384_auto(),
            Self::Sha512 => auto::vg_md_hash_sha512_auto(),
            Self::Sha512_224 => auto::vg_md_hash_sha512_224_auto(),
            Self::Sha512_256 => auto::vg_md_hash_sha512_256_auto(),
        };
        t.as_ptr()
    }

    /// Its table of `Hmac`, as the verified functions take it.
    pub(crate) fn hmac_table(self) -> *const [usize; 6] {
        let t: &'static fn_tables::Hmac = match self {
            Self::Md5 => auto::vg_hmac_md5_auto(),
            Self::Sha1 => auto::vg_hmac_sha1_auto(),
            Self::Sha224 => auto::vg_hmac_sha224_auto(),
            Self::Sha256 => auto::vg_hmac_sha256_auto(),
            Self::Sha384 => auto::vg_hmac_sha384_auto(),
            Self::Sha512 => auto::vg_hmac_sha512_auto(),
            Self::Sha512_224 => auto::vg_hmac_sha512_224_auto(),
            Self::Sha512_256 => auto::vg_hmac_sha512_256_auto(),
        };
        t.as_ptr()
    }
}

#[cfg(test)]
mod tests {
    use super::TableHash;

    /// A table of `Hash` holds the hash function's index and digest length
    /// (its words 3 and 4), as its table of `MdHash` does (words 5 and 6),
    /// and its table of `Hmac` holds them and HMAC's block size (words 3, 4
    /// and 5); and the indices are those of `VG.Spec.Mgf1.hashes`, in this
    /// order: for the tables this CPU runs.
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
        for (i, (h, len, block)) in all.into_iter().enumerate() {
            #[cfg(feature = "alloc")]
            {
                // SAFETY: `as_ptr` points to the tables' words, of
                // immutable `'static` `repr(C)` values of 5 and 11
                // pointer-sized words.
                let (g, md) = unsafe { (*h.hash_table(), *h.md_hash_table()) };
                assert_eq!((g[3], g[4]), (i, len), "{h:?}");
                assert_eq!((md[5], md[6]), (i, len), "{h:?}");
            }
            // SAFETY: `as_ptr` points to the table's words, of an
            // immutable `'static` `repr(C)` value of 6 pointer-sized
            // words.
            let m = unsafe { *h.hmac_table() };
            assert_eq!((m[3], m[4], m[5]), (i, len, block), "{h:?}");
        }
    }
}
