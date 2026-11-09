//! The hash functions as the tables of functions that RSASSA-PSS's verified
//! functions take.

use super::Hash;
use crate::hashes::tables::TableHash;

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
/// argument `hash`: the words of the best of its tables of `MdHash` that
/// this CPU runs.
pub(super) fn md_table(hash: Hash) -> super::MdTable {
    table_hash(hash).md_hash_table()
}

/// MGF1's hash function `hash` as the verified functions take it, their
/// argument `mgf1`: the words of its table of `Hash`.
pub(super) fn table(hash: Hash) -> super::Table {
    table_hash(hash).hash_table()
}

#[cfg(test)]
mod tests {
    use super::{Hash, md_table, table};

    /// The tables of each hash function hold its digest length, the one the
    /// verified functions take the hash value's to be: a table of `MdHash`
    /// in its word 6, one of `Hash` in its word 4. (`crate::hashes::tables`
    /// checks the tables' indices.)
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
        for h in all {
            // SAFETY: the pointers point to the tables' words, of immutable
            // `'static` `repr(C)` values of 11 and 5 pointer-sized words.
            let (md, g) = unsafe { (*md_table(h), *table(h)) };
            assert_eq!(md[6], h.digest_len(), "{h:?}");
            assert_eq!(g[4], h.digest_len(), "{h:?}");
        }
    }
}
