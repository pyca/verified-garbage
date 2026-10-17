//! Signing with the hash function as an argument, on x86-64: one verified
//! function per curve (`vg_ecdsa_<curve>_rfc6979_sign`, contract
//! `VG.Spec.Ecdsa.Rfc6979.Instance.signAnyContract`) signs with SHA-1 or
//! any SHA-2 function, by its number (`VG.Spec.HashId.hmac`), calling the
//! implementation of each hash function of a tier ([`Tier`]): the one this
//! CPU runs, with its multiplication.
//!
//! [`Tier`]: crate::hashes::tier::Tier

#![cfg(target_arch = "x86_64")]

use super::Error;
use crate::hashes::HashFunction;
use crate::hashes::sha1::Sha1;
use crate::hashes::sha224::Sha224;
use crate::hashes::sha256::Sha256;
use crate::hashes::sha384::Sha384;
use crate::hashes::sha512::Sha512;
use crate::hashes::sha512_224::Sha512_224;
use crate::hashes::sha512_256::Sha512_256;
use crate::zeroize::zeroize;

/// A hash function and its number, as the verified functions take it
/// (`VG.Spec.HashId.hmac`).
pub(super) trait HashId: HashFunction {
    const ID: usize;
}

impl HashId for Sha1 {
    const ID: usize = 1;
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

impl HashId for Sha512_224 {
    const ID: usize = 6;
}

impl HashId for Sha512_256 {
    const ID: usize = 7;
}

/// A verified `vg_ecdsa_<curve>_rfc6979_sign`, for scalars of `Q` bytes and
/// signatures of `S`.
pub(super) type SignFn<const Q: usize, const S: usize> = unsafe extern "sysv64" fn(
    *mut [u8; S],
    *const [u8; Q],
    *const u8,
    usize,
    *mut [u64; 1024],
    usize,
) -> u32;

/// The signature `r ‖ s` of `digest`, a hash with the function numbered
/// `hash`, with the key `d`, by `sign`.
///
/// # Safety
///
/// `sign` needs no CPU feature that this CPU lacks, and `hash` is one of
/// 1..=7 (a [`HashId::ID`]) whose function's output is as long as `digest`.
pub(super) unsafe fn sign<const Q: usize, const S: usize>(
    sign: SignFn<Q, S>,
    d: &[u8; Q],
    digest: &[u8],
    hash: usize,
) -> Result<[u8; S], Error> {
    let mut out = [0; S];
    let mut scratch = [0u64; 1024];
    // SAFETY: `out` is valid for reads and writes of `S` bytes, `d` for reads
    // of `Q`, `digest` of its length (the output length of the hash function
    // `hash` names, one of 1..=7, as the caller guarantees) and `scratch` for reads
    // and writes of 8192; `out` and `scratch` are distinct objects from each
    // other and the others, so none overlaps another or the call's stack
    // frame, and, as Rust objects, none wraps around the address space. The
    // caller guarantees the CPU features `sign` needs.
    let ok = unsafe {
        sign(
            &mut out,
            d,
            digest.as_ptr(),
            digest.len(),
            &mut scratch,
            hash,
        )
    };
    zeroize(&mut scratch);
    if ok == 1 {
        Ok(out)
    } else {
        Err(Error::InvalidKey)
    }
}

/// The `Q` bytes whose leftmost `8 Q - sh` bits, as an integer, are that of
/// the leftmost bits of `digest`, as many as the curve's order has (FIPS
/// 186-5 §6.4.2), for an order of `8 Q - sh` bits: verification's `e`. A
/// digest shorter than that is its integer (`sh` is 0 for a curve whose
/// scalars are no longer than every digest).
pub(super) fn leftmost<const Q: usize>(digest: &[u8], sh: u32) -> [u8; Q] {
    let mut e = [0; Q];
    if digest.len() >= Q {
        e.copy_from_slice(&digest[..Q]);
    } else {
        let o = Q - digest.len();
        for (i, &b) in digest.iter().enumerate() {
            let v = u16::from(b) << sh;
            e[o + i] |= v as u8;
            e[o + i - 1] |= (v >> 8) as u8;
        }
    }
    e
}

/// Signing over the curve `$curve` with each of SHA-1 and the SHA-2
/// functions, by the function `$sign` chooses for this CPU's features
/// (`SignFn`, `super::rfc6979_x86_64`), and verification by `$verify` of `e`, the hash's leftmost
/// bits (`leftmost`, for an order of `8 Q - $sh` bits).
macro_rules! any_hash {
    ($curve:ty, $sign:path, $verify:path, $sh:expr) => {
        $crate::ecdsa::rfc6979::any_hash!(
            @each $curve, $sign, $verify, $sh,
            sha1::Sha1, sha224::Sha224, sha256::Sha256, sha384::Sha384, sha512::Sha512,
            sha512_224::Sha512_224, sha512_256::Sha512_256
        );
    };
    (@each $curve:ty, $sign:path, $verify:path, $sh:expr, $($m:ident::$h:ident),*) => {
        $(
            $crate::ecdsa::rfc6979::any_hash!(
                @one $curve, $sign, $verify, $sh, $crate::hashes::$m::$h
            );
        )*
    };
    (@one $curve:ty, $sign:path, $verify:path, $sh:expr, $h:ty) => {
        impl $crate::ecdsa::sealed::Functions<$curve> for $h {
            fn sign(
                d: &<$curve as $crate::ecdsa::Curve>::PrivateKey,
                digest: &<$h as $crate::hashes::HashFunction>::Output,
            ) -> Result<<$curve as $crate::ecdsa::Curve>::Signature, $crate::ecdsa::Error> {
                let sign = $sign($crate::cpu::detected());
                // SAFETY: `$sign` chooses a function that needs no CPU
                // feature that this CPU lacks, and `digest` is a hash with
                // the function `$h`, numbered `ID`.
                unsafe {
                    $crate::ecdsa::rfc6979::sign(
                        sign,
                        d,
                        digest.as_ref(),
                        <$h as $crate::ecdsa::rfc6979::HashId>::ID,
                    )
                }
            }

            fn verify(
                q: &<$curve as $crate::ecdsa::Curve>::PublicKey,
                digest: &<$h as $crate::hashes::HashFunction>::Output,
                signature: &<$curve as $crate::ecdsa::Curve>::Signature,
            ) -> Result<(), $crate::ecdsa::Error> {
                $verify(q, &$crate::ecdsa::rfc6979::leftmost(digest.as_ref(), $sh), signature)
            }
        }

        impl $crate::ecdsa::SignatureHash<$curve> for $h {}
    };
}
pub(super) use any_hash;

#[cfg(test)]
mod tests {
    use super::leftmost;

    #[test]
    fn leftmost_bits() {
        let digest: [u8; 4] = [0x81, 0x02, 0x03, 0xff];
        assert_eq!(leftmost::<2>(&digest, 0), [0x81, 0x02]);
        assert_eq!(leftmost::<6>(&digest, 0), [0, 0, 0x81, 0x02, 0x03, 0xff]);
        // Shifted left by 7 bits: the integer of the leftmost 41 of 48 bits.
        assert_eq!(leftmost::<6>(&digest, 7), [0, 0x40, 0x81, 0x01, 0xff, 0x80]);
    }
}
