//! The hash functions as the tables of functions that RSAES-OAEP's verified
//! functions take.

use super::Hash;
use crate::hashes::tables::TableHash;

/// The hash function `hash` as the verified functions take it: the words of
/// the best table of `Hash` that this CPU runs.
pub(super) fn table(hash: Hash) -> super::Table {
    let h = match hash {
        Hash::Sha1 => TableHash::Sha1,
        Hash::Sha224 => TableHash::Sha224,
        Hash::Sha256 => TableHash::Sha256,
        Hash::Sha384 => TableHash::Sha384,
        Hash::Sha512 => TableHash::Sha512,
        Hash::Sha512_224 => TableHash::Sha512_224,
        Hash::Sha512_256 => TableHash::Sha512_256,
    };
    h.hash_table()
}

#[cfg(test)]
mod tests {
    use super::{Hash, table};

    /// Every hash function has a table, whose word 4 is
    /// the hash function's digest length, which encryption takes as the
    /// seed's.
    #[test]
    fn tables() {
        let all = [
            Hash::Sha1,
            Hash::Sha224,
            Hash::Sha256,
            Hash::Sha384,
            Hash::Sha512,
            Hash::Sha512_224,
            Hash::Sha512_256,
        ];
        for h in all {
            let t = table(h);
            // SAFETY: `t` points to a table's five words, of an
            // immutable `'static` `repr(C)` value.
            assert_eq!(unsafe { (*t)[4] }, h.digest_len(), "{h:?}");
        }
    }
}
