//! ECDSA's signatures on x86-64: one verified function for each curve
//! (`vg_ecdsa_<curve>_sign`, and `_adx` for the curves with BMI2 and ADX
//! multiplications; contract
//! `VG.Spec.Ecdsa.Rfc6979.TableInstance.signContract`), which takes the hash
//! function as a table (`crate::arch::fn_tables`), so that a curve signs
//! with every hash function that has HMAC: MD5, SHA-1 and the SHA-2 family
//! ([`TableHash`]). Each hash function's table is the one for the
//! implementation its backend chooses for this CPU, as with its other uses
//! (`TableHash::table`).

#![cfg(target_arch = "x86_64")]

use super::Error;
use crate::arch::fn_tables::{
    Hash, VG_HASH_MD5, VG_HASH_SHA1, VG_HASH_SHA1_SHANI, VG_HASH_SHA1_SHANI_FEATURES,
    VG_HASH_SHA224, VG_HASH_SHA224_AVX2, VG_HASH_SHA224_AVX2_FEATURES, VG_HASH_SHA224_SHANI,
    VG_HASH_SHA224_SHANI_FEATURES, VG_HASH_SHA256, VG_HASH_SHA256_AVX2,
    VG_HASH_SHA256_AVX2_FEATURES, VG_HASH_SHA256_SHANI, VG_HASH_SHA256_SHANI_FEATURES,
    VG_HASH_SHA384, VG_HASH_SHA384_AVX2, VG_HASH_SHA384_AVX2_FEATURES, VG_HASH_SHA384_SHANI,
    VG_HASH_SHA384_SHANI_FEATURES, VG_HASH_SHA512, VG_HASH_SHA512_224, VG_HASH_SHA512_224_AVX2,
    VG_HASH_SHA512_224_AVX2_FEATURES, VG_HASH_SHA512_224_SHANI, VG_HASH_SHA512_224_SHANI_FEATURES,
    VG_HASH_SHA512_256, VG_HASH_SHA512_256_AVX2, VG_HASH_SHA512_256_AVX2_FEATURES,
    VG_HASH_SHA512_256_SHANI, VG_HASH_SHA512_256_SHANI_FEATURES, VG_HASH_SHA512_AVX2,
    VG_HASH_SHA512_AVX2_FEATURES, VG_HASH_SHA512_SHANI, VG_HASH_SHA512_SHANI_FEATURES,
};
use crate::hashes::HashFunction;
use crate::hashes::md5::{Md5, Md5Backend};
use crate::hashes::sha1::{Sha1, Sha1Backend};
use crate::hashes::sha224::{Sha224, Sha224Backend};
use crate::hashes::sha256::{Sha256, Sha256Backend};
use crate::hashes::sha384::{Sha384, Sha384Backend};
use crate::hashes::sha512::{Sha512, Sha512Backend};
use crate::hashes::sha512_224::{Sha512_224, Sha512_224Backend};
use crate::hashes::sha512_256::{Sha512_256, Sha512_256Backend};
use crate::zeroize::zeroize;
use verified_garbage_cpu::Features;

/// A hash function that the verified signatures take as a table: one with
/// HMAC (`VG.Spec.Ecdsa.Rfc6979.hmacOf`).
pub trait TableHash: HashFunction {
    /// The table of the implementation that a CPU with the features `f`
    /// runs (as the hash function's backend chooses), with the features its
    /// functions need.
    fn table(f: Features) -> (&'static Hash, Features);
}

const NONE: Features = Features(0);

impl TableHash for Md5 {
    fn table(f: Features) -> (&'static Hash, Features) {
        match Md5Backend::select(f) {
            Md5Backend::Scalar => (&VG_HASH_MD5, NONE),
        }
    }
}

impl TableHash for Sha1 {
    fn table(f: Features) -> (&'static Hash, Features) {
        match Sha1Backend::select(f) {
            Sha1Backend::Scalar => (&VG_HASH_SHA1, NONE),
            Sha1Backend::ShaNi => (&VG_HASH_SHA1_SHANI, VG_HASH_SHA1_SHANI_FEATURES),
        }
    }
}

impl TableHash for Sha224 {
    fn table(f: Features) -> (&'static Hash, Features) {
        match Sha224Backend::select(f) {
            Sha224Backend::Scalar => (&VG_HASH_SHA224, NONE),
            Sha224Backend::ShaNi => (&VG_HASH_SHA224_SHANI, VG_HASH_SHA224_SHANI_FEATURES),
            Sha224Backend::Avx2 => (&VG_HASH_SHA224_AVX2, VG_HASH_SHA224_AVX2_FEATURES),
        }
    }
}

impl TableHash for Sha256 {
    fn table(f: Features) -> (&'static Hash, Features) {
        match Sha256Backend::select(f) {
            Sha256Backend::Scalar => (&VG_HASH_SHA256, NONE),
            Sha256Backend::ShaNi => (&VG_HASH_SHA256_SHANI, VG_HASH_SHA256_SHANI_FEATURES),
            Sha256Backend::Avx2 => (&VG_HASH_SHA256_AVX2, VG_HASH_SHA256_AVX2_FEATURES),
        }
    }
}

impl TableHash for Sha384 {
    fn table(f: Features) -> (&'static Hash, Features) {
        match Sha384Backend::select(f) {
            Sha384Backend::Scalar => (&VG_HASH_SHA384, NONE),
            Sha384Backend::ShaNi => (&VG_HASH_SHA384_SHANI, VG_HASH_SHA384_SHANI_FEATURES),
            Sha384Backend::Avx2 => (&VG_HASH_SHA384_AVX2, VG_HASH_SHA384_AVX2_FEATURES),
        }
    }
}

impl TableHash for Sha512 {
    fn table(f: Features) -> (&'static Hash, Features) {
        match Sha512Backend::select(f) {
            Sha512Backend::Scalar => (&VG_HASH_SHA512, NONE),
            Sha512Backend::ShaNi => (&VG_HASH_SHA512_SHANI, VG_HASH_SHA512_SHANI_FEATURES),
            Sha512Backend::Avx2 => (&VG_HASH_SHA512_AVX2, VG_HASH_SHA512_AVX2_FEATURES),
        }
    }
}

impl TableHash for Sha512_224 {
    fn table(f: Features) -> (&'static Hash, Features) {
        match Sha512_224Backend::select(f) {
            Sha512_224Backend::Scalar => (&VG_HASH_SHA512_224, NONE),
            Sha512_224Backend::ShaNi => {
                (&VG_HASH_SHA512_224_SHANI, VG_HASH_SHA512_224_SHANI_FEATURES)
            }
            Sha512_224Backend::Avx2 => (&VG_HASH_SHA512_224_AVX2, VG_HASH_SHA512_224_AVX2_FEATURES),
        }
    }
}

impl TableHash for Sha512_256 {
    fn table(f: Features) -> (&'static Hash, Features) {
        match Sha512_256Backend::select(f) {
            Sha512_256Backend::Scalar => (&VG_HASH_SHA512_256, NONE),
            Sha512_256Backend::ShaNi => {
                (&VG_HASH_SHA512_256_SHANI, VG_HASH_SHA512_256_SHANI_FEATURES)
            }
            Sha512_256Backend::Avx2 => (&VG_HASH_SHA512_256_AVX2, VG_HASH_SHA512_256_AVX2_FEATURES),
        }
    }
}

/// A verified `vg_ecdsa_<curve>_sign`, for scalars of `Q` bytes and
/// signatures of `S = 2 Q`.
pub(super) type SignFn<const Q: usize, const S: usize> = unsafe extern "sysv64" fn(
    *mut [u8; S],
    *const [u8; Q],
    *const u8,
    usize,
    *mut [u64; 1024],
    *const [usize; 5],
) -> u32;

/// The signature `r ‖ s` of `digest`, the hash of a message with `H`, with
/// the key `d`, by `sign` with `H`'s table for this CPU (`f`, its features).
///
/// # Safety
///
/// `sign` needs no CPU feature that this CPU lacks.
pub(super) unsafe fn sign_with<H: TableHash, const Q: usize, const S: usize>(
    sign: SignFn<Q, S>,
    f: Features,
    d: &[u8; Q],
    digest: &H::Output,
) -> Result<[u8; S], Error> {
    let (table, _) = H::table(f);
    let digest = digest.as_ref();
    let mut out = [0; S];
    let mut scratch = [0u64; 1024];
    // SAFETY: `out` is valid for reads and writes of `S` bytes, `d` for
    // reads of `Q`, `digest` for reads of its length, `H`'s digest length,
    // which the table `table` names, and `scratch` for reads and writes of
    // 8192; `out` and `scratch` are distinct objects from each other and the
    // others, so none overlaps another or the call's stack frame, and, as
    // Rust objects, none wraps around the address space. `table` is one of
    // the tables of the interface `Hash`, for `H`, whose functions need no
    // CPU feature that `f`, this CPU's, lacks (`TableHash::table`); the
    // caller guarantees the features `sign` needs.
    let ok = unsafe {
        sign(
            &mut out,
            d,
            digest.as_ptr(),
            digest.len(),
            &mut scratch,
            table.as_ptr(),
        )
    };
    zeroize(&mut scratch);
    if ok == 1 {
        Ok(out)
    } else {
        Err(Error::InvalidKey)
    }
}

/// The integer of a hash's leftmost bits, as many as the curve's order has
/// (FIPS 186-5 §6.4.2), as `Q` bytes, most significant first, for an order
/// of `8 Q` bits or a hash shorter than it: the hash's first `Q` bytes, or
/// the hash after zeros.
pub(super) fn leftmost<const Q: usize>(digest: &[u8]) -> [u8; Q] {
    let mut e = [0; Q];
    if digest.len() >= Q {
        e.copy_from_slice(&digest[..Q]);
    } else {
        e[Q - digest.len()..].copy_from_slice(digest);
    }
    e
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpu::NAMES;

    /// The digest length a table names (its word 4).
    fn table_len(t: &'static Hash) -> usize {
        // SAFETY: `as_ptr` points to the table's five words, of an immutable
        // `'static` `repr(C)` value of five pointer-sized words.
        unsafe { (*t.as_ptr())[4] }
    }

    /// `H`'s tables: their functions need no CPU feature that was not
    /// required to choose them, and they name `H`'s digest length.
    fn check<H: TableHash>(f: Features) {
        let (t, need) = H::table(f);
        assert!(f.contains(need));
        assert_eq!(table_len(t), H::OUTPUT_SIZE);
    }

    #[test]
    fn tables() {
        for bits in 0..1u32 << NAMES.len() {
            let f = Features(bits);
            check::<Md5>(f);
            check::<Sha1>(f);
            check::<Sha224>(f);
            check::<Sha256>(f);
            check::<Sha384>(f);
            check::<Sha512>(f);
            check::<Sha512_224>(f);
            check::<Sha512_256>(f);
        }
    }
}
