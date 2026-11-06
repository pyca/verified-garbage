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
use verified_garbage_cpu::Features;

/// A hash function that the verified signatures take HMAC over as a table:
/// one with HMAC (`VG.Spec.HmacTable.hmacOf`).
pub trait HmacHash: HashFunction {
    /// Its table of `Hmac`, as the verified functions take it, for the
    /// implementation that a CPU with the features `f` runs best
    /// (`TableHash::hmac_table`).
    fn hmac_table(f: Features) -> *const [usize; 6];
}

impl HmacHash for Md5 {
    fn hmac_table(f: Features) -> *const [usize; 6] {
        TableHash::Md5.hmac_table(f)
    }
}

impl HmacHash for Sha1 {
    fn hmac_table(f: Features) -> *const [usize; 6] {
        TableHash::Sha1.hmac_table(f)
    }
}

impl HmacHash for Sha224 {
    fn hmac_table(f: Features) -> *const [usize; 6] {
        TableHash::Sha224.hmac_table(f)
    }
}

impl HmacHash for Sha256 {
    fn hmac_table(f: Features) -> *const [usize; 6] {
        TableHash::Sha256.hmac_table(f)
    }
}

impl HmacHash for Sha384 {
    fn hmac_table(f: Features) -> *const [usize; 6] {
        TableHash::Sha384.hmac_table(f)
    }
}

impl HmacHash for Sha512 {
    fn hmac_table(f: Features) -> *const [usize; 6] {
        TableHash::Sha512.hmac_table(f)
    }
}

impl HmacHash for Sha512_224 {
    fn hmac_table(f: Features) -> *const [usize; 6] {
        TableHash::Sha512_224.hmac_table(f)
    }
}

impl HmacHash for Sha512_256 {
    fn hmac_table(f: Features) -> *const [usize; 6] {
        TableHash::Sha512_256.hmac_table(f)
    }
}

/// A verified `vg_ecdsa_<curve>_sign`, for scalars of `Q` bytes and
/// signatures of `S = 2 Q`.
#[cfg(target_arch = "x86_64")]
pub(super) type SignFn<const Q: usize, const S: usize> = unsafe extern "sysv64" fn(
    *mut [u8; S],
    *const [u8; Q],
    *const u8,
    usize,
    *mut [u64; 1024],
    *const [usize; 6],
) -> u32;

/// A verified `vg_ecdsa_<curve>_sign`, for scalars of `Q` bytes and
/// signatures of `S = 2 Q`.
#[cfg(not(target_arch = "x86_64"))]
pub(super) type SignFn<const Q: usize, const S: usize> = unsafe extern "C" fn(
    *mut [u8; S],
    *const [u8; Q],
    *const u8,
    usize,
    *mut [u64; 1024],
    *const [usize; 6],
) -> u32;

/// The signature `r ‖ s` of `digest`, the hash of a message with `H`, with
/// the key `d`, by `sign` with `H`'s table of `Hmac` for this CPU (`f`, its
/// features).
///
/// # Safety
///
/// `sign` needs no CPU feature that this CPU lacks.
pub(super) unsafe fn sign_with<H: HmacHash, const Q: usize, const S: usize>(
    sign: SignFn<Q, S>,
    f: Features,
    d: &[u8; Q],
    digest: &H::Output,
) -> Result<[u8; S], InvalidKey> {
    let table = H::hmac_table(f);
    let digest = digest.as_ref();
    let mut out = [0; S];
    let mut scratch = [0u64; 1024];
    // SAFETY: `out` is valid for reads and writes of `S` bytes, `d` for
    // reads of `Q`, `digest` for reads of its length, `H`'s digest length,
    // which the table `table` names, and `scratch` for reads and writes of
    // 8192; `out` and `scratch` are distinct objects from each other and the
    // others, so none overlaps another or the call's stack frame, and, as
    // Rust objects, none wraps around the address space. `table` is one of
    // the tables of the interface `Hmac`, for `H`, whose functions need no
    // CPU feature that `f`, this CPU's, lacks (`TableHash::hmac_table`); the
    // caller guarantees the features `sign` needs.
    let ok = unsafe {
        sign(
            &mut out,
            d,
            digest.as_ptr(),
            digest.len(),
            &mut scratch,
            table,
        )
    };
    zeroize(&mut scratch);
    if ok == 1 { Ok(out) } else { Err(InvalidKey) }
}

#[cfg(test)]
mod tests {
    use super::{HmacHash, Md5, Sha1, Sha224, Sha256, Sha384, Sha512, Sha512_224, Sha512_256};
    use verified_garbage_cpu::Features;

    /// `H`'s table of `Hmac` names `H`'s digest length and HMAC's block
    /// size (its words 4 and 5).
    fn check<H: HmacHash>() {
        // SAFETY: `hmac_table` points to the table's six words, of an
        // immutable `'static` `repr(C)` value of six pointer-sized words.
        let t = unsafe { *H::hmac_table(Features(0)) };
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
