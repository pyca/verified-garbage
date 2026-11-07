//! HMAC over each hash function ([`HmacHash`]) as the table of functions that
//! deterministic ECDSA's signing takes.

use crate::error::InvalidKey;
use crate::hashes::HashFunction;
use crate::hashes::md5::Md5;
use crate::hashes::sha1::Sha1;
use crate::hashes::sha224::Sha224;
use crate::hashes::sha256::Sha256;
use crate::hashes::sha384::Sha384;
use crate::hashes::sha512::Sha512;
use crate::hashes::sha512_224::Sha512_224;
use crate::hashes::sha512_256::Sha512_256;
use crate::hashes::tables::TableHash;
use crate::zeroize::zeroize;

/// A hash function that the verified signatures take HMAC over as a table:
/// one with HMAC (`VG.Spec.HmacTable.hmacOf`).
pub trait HmacHash: HashFunction {
    /// The best of its tables of `Hmac` that this CPU runs, as the verified
    /// functions take it (`TableHash::hmac_table`).
    fn hmac_table() -> *const [usize; 6];
}

impl HmacHash for Md5 {
    fn hmac_table() -> *const [usize; 6] {
        TableHash::Md5.hmac_table()
    }
}

impl HmacHash for Sha1 {
    fn hmac_table() -> *const [usize; 6] {
        TableHash::Sha1.hmac_table()
    }
}

impl HmacHash for Sha224 {
    fn hmac_table() -> *const [usize; 6] {
        TableHash::Sha224.hmac_table()
    }
}

impl HmacHash for Sha256 {
    fn hmac_table() -> *const [usize; 6] {
        TableHash::Sha256.hmac_table()
    }
}

impl HmacHash for Sha384 {
    fn hmac_table() -> *const [usize; 6] {
        TableHash::Sha384.hmac_table()
    }
}

impl HmacHash for Sha512 {
    fn hmac_table() -> *const [usize; 6] {
        TableHash::Sha512.hmac_table()
    }
}

impl HmacHash for Sha512_224 {
    fn hmac_table() -> *const [usize; 6] {
        TableHash::Sha512_224.hmac_table()
    }
}

impl HmacHash for Sha512_256 {
    fn hmac_table() -> *const [usize; 6] {
        TableHash::Sha512_256.hmac_table()
    }
}

/// The signature `r ‖ s` of `digest`, the hash of a message with `H`, with
/// the key `d`, by `sign`, a curve's `vg_ecdsa_<curve>_sign_auto`, which it
/// calls with the signature's buffer, `d`, `digest`, 1024 words of working
/// space and the best of `H`'s tables of `Hmac` that this CPU runs.
///
/// Each is valid for reads (and the signature and working space for writes)
/// of its length, and they are distinct objects, so none overlaps another
/// or the call's stack frame, and, as Rust objects, none wraps around the
/// address space; `digest` is as long as `H`'s digest, which the table names,
/// and the table is one of the interface `Hmac`'s, for `H`, whose functions
/// need no CPU feature that this CPU lacks (its dispatcher chose it,
/// `TableHash::hmac_table`).
pub(super) fn sign_with<H: HmacHash, const Q: usize, const S: usize>(
    sign: impl FnOnce(&mut [u8; S], &[u8; Q], &[u8], &mut [u64; 1024], *const [usize; 6]) -> u32,
    d: &[u8; Q],
    digest: &H::Output,
) -> Result<[u8; S], InvalidKey> {
    let table = H::hmac_table();
    let mut out = [0; S];
    let mut scratch = [0u64; 1024];
    let ok = sign(&mut out, d, digest.as_ref(), &mut scratch, table);
    zeroize(&mut scratch);
    if ok == 1 { Ok(out) } else { Err(InvalidKey) }
}

#[cfg(test)]
mod tests {
    use super::{HmacHash, Md5, Sha1, Sha224, Sha256, Sha384, Sha512, Sha512_224, Sha512_256};

    /// `H`'s table of `Hmac` names `H`'s digest length and HMAC's block
    /// size (its words 4 and 5).
    fn check<H: HmacHash>() {
        // SAFETY: `hmac_table` points to the table's six words, of an
        // immutable `'static` `repr(C)` value of six pointer-sized words.
        let t = unsafe { *H::hmac_table() };
        assert_eq!((t[4], t[5]), (H::OUTPUT_SIZE, H::BLOCK_SIZE));
    }

    #[test]
    fn tables() {
        check::<Md5>();
        check::<Sha1>();
        check::<Sha224>();
        check::<Sha256>();
        check::<Sha384>();
        check::<Sha512>();
        check::<Sha512_224>();
        check::<Sha512_256>();
    }
}
