//! The hash functions as the tables of functions that RSAES-OAEP's verified
//! functions take.

use crate::hashes::tables::TableHash;
use crate::rsa::pkcs1_sig::Hash;

/// The hash function `hash` as the verified functions take it: the words of
/// the best of its tables of `Hash` that this CPU runs, or `None` if `hash` is not supported (MD5, which RSAES-OAEP
/// does not use, and SHA-3's, which have no table).
pub(super) fn table(hash: Hash) -> Option<super::Table> {
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
    Some(h.hash_table())
}

#[cfg(test)]
mod tests {
    use super::{Hash, table};

    /// Every hash function but MD5 and SHA-3's has a table, whose word 4 is
    /// the hash function's digest length, which encryption takes as the
    /// seed's.
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
        let mut n = 0;
        for h in all {
            if let Some(t) = table(h) {
                // SAFETY: `t` points to a table's five words, of an
                // immutable `'static` `repr(C)` value.
                assert_eq!(unsafe { (*t)[4] }, h.digest_len(), "{h:?}");
                n += 1;
            }
        }
        assert_eq!(n, 7);
    }
}
