//! ECDSA on x86-64: deterministic signatures (RFC 6979 §3.2) with HMAC with
//! SHA-1 or any SHA-2 function, by one verified function per curve,
//! `vg_ecdsa_<curve>_rfc6979_sign` (contract
//! `VG.Spec.Ecdsa.Rfc6979.Instance.signAnyContract`), which takes the hash
//! function as its number and the table of its streaming functions
//! (`crate::hash_fns`), and calls them; each with BMI2 and ADX where the
//! curve's multiplications have them (`_adx`). Verification takes the hash's
//! leftmost bits, as many as the curve's order has (FIPS 186-5 §6.4.2).

#![cfg(target_arch = "x86_64")]

use super::{
    BrainpoolP256r1, BrainpoolP384r1, BrainpoolP512r1, Error, P192, P224, P256, P384, P521,
    Secp256k1, SignatureHash, sealed,
};
use crate::arch::ecdsa_brainpoolp256r1_rfc6979::vg_ecdsa_brainpoolp256r1_rfc6979_sign;
use crate::arch::ecdsa_brainpoolp384r1_rfc6979::vg_ecdsa_brainpoolp384r1_rfc6979_sign;
use crate::arch::ecdsa_brainpoolp512r1_rfc6979::vg_ecdsa_brainpoolp512r1_rfc6979_sign;
use crate::arch::ecdsa_p192_rfc6979::vg_ecdsa_p192_rfc6979_sign;
use crate::arch::ecdsa_p224_rfc6979::vg_ecdsa_p224_rfc6979_sign;
use crate::arch::ecdsa_p256_rfc6979::{vg_ecdsa_p256_rfc6979_sign, vg_ecdsa_p256_rfc6979_sign_adx};
use crate::arch::ecdsa_p384_rfc6979::{vg_ecdsa_p384_rfc6979_sign, vg_ecdsa_p384_rfc6979_sign_adx};
use crate::arch::ecdsa_p521_rfc6979::{vg_ecdsa_p521_rfc6979_sign, vg_ecdsa_p521_rfc6979_sign_adx};
use crate::arch::ecdsa_secp256k1_rfc6979::vg_ecdsa_secp256k1_rfc6979_sign;
use crate::cpu::{Features, detected};
use crate::hash_fns::{self, Table};
use crate::hashes::sha1::Sha1;
use crate::hashes::sha224::Sha224;
use crate::hashes::sha256::Sha256;
use crate::hashes::sha384::Sha384;
use crate::hashes::sha512::Sha512;
use crate::hashes::sha512_224::Sha512_224;
use crate::hashes::sha512_256::Sha512_256;
use crate::zeroize::zeroize;

/// A verified `vg_ecdsa_<curve>_rfc6979_sign`, for scalars of `Q` bytes and
/// signatures of `S`.
type SignFn<const Q: usize, const S: usize> = unsafe extern "sysv64" fn(
    *mut [u8; S],
    *const [u8; Q],
    *const u8,
    usize,
    *mut [u64; 1024],
    usize,
    *const [u64; 3],
) -> u32;

/// The signature `r ‖ s` of `digest` with the key `d`, by `sign` with the
/// hash function of the table `t`.
///
/// # Safety
///
/// `sign` and the functions of `t` need no CPU feature that this CPU lacks,
/// and `digest` is as long as the values of `t`'s hash function.
unsafe fn sign_with<const Q: usize, const S: usize>(
    sign: SignFn<Q, S>,
    t: Table,
    d: &[u8; Q],
    digest: &[u8],
) -> Result<[u8; S], Error> {
    let mut out = [0; S];
    let mut scratch = [0u64; 1024];
    // SAFETY: `out` is valid for reads and writes of `S = 2 Q` bytes, `d` for
    // reads of `Q`, `digest` of `digest.len()`, `scratch` for reads and
    // writes of 8192 and `t.fns` for reads of 24; `out` and `scratch` are
    // distinct objects from each other and the others, so none overlaps
    // another or the call's stack frame, and, as Rust objects, none wraps
    // around the address space. `t.id` is the number of SHA-1 or a SHA-2
    // function (`hash_fns`), `t.fns` the addresses of its streaming
    // functions, for implementations the CPU can run, and `digest` as long
    // as its values (the caller); and the CPU has the features of `sign`
    // (the caller).
    let ok = unsafe {
        sign(
            &mut out,
            d,
            digest.as_ptr(),
            digest.len(),
            &mut scratch,
            t.id,
            &t.fns,
        )
    };
    zeroize(&mut scratch);
    if ok == 1 {
        Ok(out)
    } else {
        Err(Error::InvalidKey)
    }
}

/// The leftmost `Q` bytes of `digest`, or its integer in `Q` bytes if it is
/// shorter: the hash's leftmost bits, as many as the order of a curve of
/// `8 Q`-bit order has (FIPS 186-5 §6.4.2).
fn leftmost<const Q: usize>(digest: &[u8]) -> [u8; Q] {
    let mut e = [0; Q];
    if digest.len() >= Q {
        e.copy_from_slice(&digest[..Q]);
    } else {
        e[Q - digest.len()..].copy_from_slice(digest);
    }
    e
}

/// The signing function of a curve with one implementation.
macro_rules! one {
    ($f:ident) => {
        |_: Features| $f
    };
}

/// The signing function of a curve with BMI2's and ADX's multiplications
/// (`crate::ec::<curve>::Mul`), for the CPU's features.
macro_rules! with_mul {
    ($ec:ident, $f:ident, $adx:ident) => {
        |f: Features| match crate::ec::$ec::Mul::select(f) {
            crate::ec::$ec::Mul::Baseline => $f,
            // `select` chose it because the CPU has its features.
            crate::ec::$ec::Mul::Adx => $adx,
        }
    };
}

/// ECDSA over `$curve` with each hash function, by the signing function
/// `$signer` chooses, verifying with `$verify` of the hash's leftmost bits
/// (`$e`).
macro_rules! curve {
    ($curve:ident, $q:literal, $u:literal, $s:literal, $signer:expr, $verify:path, $e:path) => {
        curve!(@hash $curve, $q, $u, $s, $signer, $verify, $e, Sha1, sha1);
        curve!(@hash $curve, $q, $u, $s, $signer, $verify, $e, Sha224, sha224);
        curve!(@hash $curve, $q, $u, $s, $signer, $verify, $e, Sha256, sha256);
        curve!(@hash $curve, $q, $u, $s, $signer, $verify, $e, Sha384, sha384);
        curve!(@hash $curve, $q, $u, $s, $signer, $verify, $e, Sha512, sha512);
        curve!(@hash $curve, $q, $u, $s, $signer, $verify, $e, Sha512_224, sha512_224);
        curve!(@hash $curve, $q, $u, $s, $signer, $verify, $e, Sha512_256, sha512_256);
    };
    (@hash $curve:ident, $q:literal, $u:literal, $s:literal, $signer:expr, $verify:path, $e:path,
        $hash:ident, $table:ident) => {
        impl sealed::Functions<$curve> for $hash {
            fn sign(d: &[u8; $q], digest: &Self::Output) -> Result<[u8; $s], Error> {
                let f = detected();
                let signer: SignFn<$q, $s> = ($signer)(f);
                // SAFETY: `select` chose `signer`, and `hash_fns` the table's
                // functions, for this CPU's features; `digest` is one of the
                // hash function's values.
                unsafe { sign_with(signer, hash_fns::$table(f), d, digest.as_ref()) }
            }

            fn verify(q: &[u8; $u], digest: &Self::Output, signature: &[u8; $s]) -> Result<(), Error> {
                $verify(q, &$e(digest.as_ref()), signature)
            }
        }

        impl SignatureHash<$curve> for $hash {}
    };
}

curve!(
    P192,
    24,
    49,
    48,
    one!(vg_ecdsa_p192_rfc6979_sign),
    super::p192::verify_with,
    leftmost
);
curve!(
    P224,
    28,
    57,
    56,
    one!(vg_ecdsa_p224_rfc6979_sign),
    super::p224::verify_with,
    leftmost
);
curve!(
    P256,
    32,
    65,
    64,
    with_mul!(
        p256,
        vg_ecdsa_p256_rfc6979_sign,
        vg_ecdsa_p256_rfc6979_sign_adx
    ),
    super::p256::verify_with,
    leftmost
);
curve!(
    P384,
    48,
    97,
    96,
    with_mul!(
        p384,
        vg_ecdsa_p384_rfc6979_sign,
        vg_ecdsa_p384_rfc6979_sign_adx
    ),
    super::p384::verify_with,
    leftmost
);
curve!(
    P521,
    66,
    133,
    132,
    with_mul!(
        p521,
        vg_ecdsa_p521_rfc6979_sign,
        vg_ecdsa_p521_rfc6979_sign_adx
    ),
    super::p521::verify_with,
    super::p521::widen
);
curve!(
    Secp256k1,
    32,
    65,
    64,
    one!(vg_ecdsa_secp256k1_rfc6979_sign),
    super::secp256k1::verify_with,
    leftmost
);
curve!(
    BrainpoolP256r1,
    32,
    65,
    64,
    one!(vg_ecdsa_brainpoolp256r1_rfc6979_sign),
    super::brainpoolp256r1::verify_with,
    leftmost
);
curve!(
    BrainpoolP384r1,
    48,
    97,
    96,
    one!(vg_ecdsa_brainpoolp384r1_rfc6979_sign),
    super::brainpoolp384r1::verify_with,
    leftmost
);
curve!(
    BrainpoolP512r1,
    64,
    129,
    128,
    one!(vg_ecdsa_brainpoolp512r1_rfc6979_sign),
    super::brainpoolp512r1::verify_with,
    leftmost
);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arch::ecdsa_p256_rfc6979::VG_ECDSA_P256_RFC6979_SIGN_ADX_FEATURES;
    use crate::arch::ecdsa_p384_rfc6979::VG_ECDSA_P384_RFC6979_SIGN_ADX_FEATURES;
    use crate::arch::ecdsa_p521_rfc6979::VG_ECDSA_P521_RFC6979_SIGN_ADX_FEATURES;
    use crate::cpu::NAMES;

    /// The signers with BMI2's and ADX's multiplications need no CPU feature
    /// that the multiplications are not selected for: on every set of
    /// features that selects them.
    #[test]
    fn adx_features() {
        for bits in 0..1u32 << NAMES.len() {
            let f = Features(bits);
            if crate::ec::p256::Mul::select(f) == crate::ec::p256::Mul::Adx {
                assert!(
                    f.contains(VG_ECDSA_P256_RFC6979_SIGN_ADX_FEATURES),
                    "{bits:#b}"
                );
            }
            if crate::ec::p384::Mul::select(f) == crate::ec::p384::Mul::Adx {
                assert!(
                    f.contains(VG_ECDSA_P384_RFC6979_SIGN_ADX_FEATURES),
                    "{bits:#b}"
                );
            }
            if crate::ec::p521::Mul::select(f) == crate::ec::p521::Mul::Adx {
                assert!(
                    f.contains(VG_ECDSA_P521_RFC6979_SIGN_ADX_FEATURES),
                    "{bits:#b}"
                );
            }
        }
    }

    /// A hash shorter than the curve's scalars is its integer; a longer one
    /// its leftmost bytes.
    #[test]
    fn leftmost_bytes() {
        assert_eq!(leftmost::<4>(&[1, 2]), [0, 0, 1, 2]);
        assert_eq!(leftmost::<2>(&[1, 2, 3]), [1, 2]);
    }
}
