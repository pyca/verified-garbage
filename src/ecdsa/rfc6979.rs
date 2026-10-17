//! Deterministic signatures on x86 with the hash function as an argument:
//! one verified function per curve and [`Tier`] of the hash functions
//! (`vg_ecdsa_<curve>_rfc6979_sign`, `…_hash_shani`, contract
//! `VG.Spec.Ecdsa.Rfc6979.Instance.signAnyContract`), which takes the hash
//! function by its number (`VG.Spec.HashId`).

#![cfg(target_arch = "x86")]

use super::Error;
use crate::cpu::detected;
use crate::hashes::HashFunction;
use crate::hashes::sha224::Sha224;
use crate::hashes::sha256::Sha256;
use crate::hashes::sha384::Sha384;
use crate::hashes::sha512::Sha512;
use crate::hashes::tier::Tier;
use crate::zeroize::zeroize;

/// A hash function, by the number the verified functions take
/// (`VG.Spec.HashId`).
pub(super) trait HashId: HashFunction {
    const ID: usize;
}

impl HashId for Sha224 {
    const ID: usize = 2;
}

impl HashId for Sha256 {
    const ID: usize = 3;
}

impl HashId for Sha384 {
    const ID: usize = 4;
}

impl HashId for Sha512 {
    const ID: usize = 5;
}

/// A verified `vg_ecdsa_<curve>_rfc6979_sign`, for scalars of `Q` bytes and
/// signatures of `S`.
pub(super) type SignFn<const Q: usize, const S: usize> = unsafe extern "C" fn(
    *mut [u8; S],
    *const [u8; Q],
    *const u8,
    usize,
    *mut [u64; 1024],
    usize,
) -> u32;

/// The signature `r ‖ s` of `digest`, the hash with `H`, with the key `d`,
/// by the curve's function of this CPU's tier: `base` or `shani`.
pub(super) fn sign<H: HashId, const Q: usize, const S: usize>(
    base: SignFn<Q, S>,
    shani: SignFn<Q, S>,
    d: &[u8; Q],
    digest: &H::Output,
) -> Result<[u8; S], Error> {
    let sign = match Tier::select(detected()) {
        Tier::Base => base,
        Tier::ShaNi => shani,
    };
    let digest = digest.as_ref();
    let mut out = [0; S];
    let mut scratch = [0u64; 1024];
    // SAFETY: `out` is valid for reads and writes of `S` bytes, `d` for
    // reads of `Q`, `digest` of `digest.len()` (`H::OUTPUT_SIZE`, the
    // length of the values of the hash function `H::ID` names, 1 to 5) and
    // `scratch` for reads and writes of 8192; `out` and `scratch` are
    // distinct objects from each other and the others, so none overlaps
    // another or the call's stack frame, and, as Rust objects, none wraps
    // around the address space. `sign` needs no CPU feature that the tier
    // selected for this CPU does not.
    let ok = unsafe {
        sign(
            &mut out,
            d,
            digest.as_ptr(),
            digest.len(),
            &mut scratch,
            H::ID,
        )
    };
    zeroize(&mut scratch);
    if ok == 1 {
        Ok(out)
    } else {
        Err(Error::InvalidKey)
    }
}
