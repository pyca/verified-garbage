//! Ed25519 (RFC 8032 §5.1), deterministic signatures from 32-byte seeds.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::ed25519::{
    VG_ED25519_KEY_PAIR_ADX_FEATURES, VG_ED25519_KEY_PAIR_IFMA_FEATURES,
    VG_ED25519_SIGN_EXPANDED_ADX_FEATURES, VG_ED25519_SIGN_EXPANDED_IFMA_FEATURES,
    VG_ED25519_VERIFY_ADX_FEATURES, VG_ED25519_VERIFY_IFMA_FEATURES, vg_ed25519_key_pair_adx,
    vg_ed25519_key_pair_avx2, vg_ed25519_key_pair_avx2_adx, vg_ed25519_key_pair_avx2_ifma,
    vg_ed25519_key_pair_ifma, vg_ed25519_key_pair_shani, vg_ed25519_key_pair_shani_adx,
    vg_ed25519_key_pair_shani_ifma, vg_ed25519_sign_expanded_adx, vg_ed25519_sign_expanded_avx2,
    vg_ed25519_sign_expanded_avx2_adx, vg_ed25519_sign_expanded_avx2_ifma,
    vg_ed25519_sign_expanded_ifma, vg_ed25519_sign_expanded_shani,
    vg_ed25519_sign_expanded_shani_adx, vg_ed25519_sign_expanded_shani_ifma, vg_ed25519_verify_adx,
    vg_ed25519_verify_avx2, vg_ed25519_verify_avx2_adx, vg_ed25519_verify_avx2_ifma,
    vg_ed25519_verify_ifma, vg_ed25519_verify_shani, vg_ed25519_verify_shani_adx,
    vg_ed25519_verify_shani_ifma,
};
use crate::arch::ed25519::{vg_ed25519_key_pair, vg_ed25519_sign_expanded, vg_ed25519_verify};
#[cfg(target_arch = "aarch64")]
use crate::arch::ed25519::{
    vg_ed25519_key_pair_sha3, vg_ed25519_sign_expanded_sha3, vg_ed25519_verify_sha3,
};
use crate::cpu::detected;
use crate::error::InvalidSignature;
use crate::hashes::sha512::Sha512Backend;
use crate::zeroize::{zeroize, zeroize_raw};
use core::mem::{MaybeUninit, size_of};
use verified_garbage_cpu::Features;

/// The field multiplications of the complete operations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Field {
    /// The baseline implementation.
    Baseline,
    /// `_adx`.
    #[cfg(target_arch = "x86_64")]
    Adx,
    /// `_ifma`.
    #[cfg(target_arch = "x86_64")]
    Ifma,
}

impl Field {
    /// The CPU features `select` requires to choose each implementation, by
    /// its discriminant: every CPU it is chosen for has them.
    #[cfg(target_arch = "x86_64")]
    const REQUIRES: &[Features] = &{
        let adx = Features::all(&[
            VG_ED25519_KEY_PAIR_ADX_FEATURES,
            VG_ED25519_SIGN_EXPANDED_ADX_FEATURES,
            VG_ED25519_VERIFY_ADX_FEATURES,
        ]);
        let ifma = Features::all(&[
            adx,
            VG_ED25519_KEY_PAIR_IFMA_FEATURES,
            VG_ED25519_SIGN_EXPANDED_IFMA_FEATURES,
            VG_ED25519_VERIFY_IFMA_FEATURES,
        ]);
        [Features(0), adx, ifma]
    };

    /// The fastest field multiplications a CPU with the features `f` can run.
    #[cfg(target_arch = "x86_64")]
    fn select(f: Features) -> Field {
        if f.contains(Self::REQUIRES[Field::Ifma as usize]) {
            Field::Ifma
        } else if f.contains(Self::REQUIRES[Field::Adx as usize]) {
            Field::Adx
        } else {
            Field::Baseline
        }
    }

    /// The field multiplications a CPU with the features `f` can run: there
    /// is only one here.
    #[cfg(not(target_arch = "x86_64"))]
    fn select(_: Features) -> Field {
        Field::Baseline
    }
}

/// Fails to compile unless the operations run with SHA-512's implementation
/// `$s` and the field's `$f` need no CPU feature, of the constants `$req`,
/// that their `select`s do not require to choose them.
#[cfg(target_arch = "x86_64")]
macro_rules! assert_pair {
    ($s:ident, $f:ident, [$($req:ident),*]) => {
        const _: () = assert!(
            Features::all(&[
                Sha512Backend::REQUIRES[Sha512Backend::$s as usize],
                Field::REQUIRES[Field::$f as usize],
            ])
            .contains(Features::all(&[$(crate::arch::ed25519::$req),*])),
            concat!(
                "an Ed25519 operation needs a CPU feature SHA-512's ",
                stringify!($s),
                " and the field's ",
                stringify!($f),
                " are not chosen for"
            )
        );
    };
}

// Key derivation, signing and verification for each pair.
#[cfg(target_arch = "x86_64")]
assert_pair!(
    Scalar,
    Adx,
    [
        VG_ED25519_KEY_PAIR_ADX_FEATURES,
        VG_ED25519_SIGN_EXPANDED_ADX_FEATURES,
        VG_ED25519_VERIFY_ADX_FEATURES
    ]
);
#[cfg(target_arch = "x86_64")]
assert_pair!(
    Scalar,
    Ifma,
    [
        VG_ED25519_KEY_PAIR_IFMA_FEATURES,
        VG_ED25519_SIGN_EXPANDED_IFMA_FEATURES,
        VG_ED25519_VERIFY_IFMA_FEATURES
    ]
);
#[cfg(target_arch = "x86_64")]
assert_pair!(
    ShaNi,
    Baseline,
    [
        VG_ED25519_KEY_PAIR_SHANI_FEATURES,
        VG_ED25519_SIGN_EXPANDED_SHANI_FEATURES,
        VG_ED25519_VERIFY_SHANI_FEATURES
    ]
);
#[cfg(target_arch = "x86_64")]
assert_pair!(
    ShaNi,
    Adx,
    [
        VG_ED25519_KEY_PAIR_SHANI_ADX_FEATURES,
        VG_ED25519_SIGN_EXPANDED_SHANI_ADX_FEATURES,
        VG_ED25519_VERIFY_SHANI_ADX_FEATURES
    ]
);
#[cfg(target_arch = "x86_64")]
assert_pair!(
    ShaNi,
    Ifma,
    [
        VG_ED25519_KEY_PAIR_SHANI_IFMA_FEATURES,
        VG_ED25519_SIGN_EXPANDED_SHANI_IFMA_FEATURES,
        VG_ED25519_VERIFY_SHANI_IFMA_FEATURES
    ]
);
#[cfg(target_arch = "x86_64")]
assert_pair!(
    Avx2,
    Baseline,
    [
        VG_ED25519_KEY_PAIR_AVX2_FEATURES,
        VG_ED25519_SIGN_EXPANDED_AVX2_FEATURES,
        VG_ED25519_VERIFY_AVX2_FEATURES
    ]
);
#[cfg(target_arch = "x86_64")]
assert_pair!(
    Avx2,
    Adx,
    [
        VG_ED25519_KEY_PAIR_AVX2_ADX_FEATURES,
        VG_ED25519_SIGN_EXPANDED_AVX2_ADX_FEATURES,
        VG_ED25519_VERIFY_AVX2_ADX_FEATURES
    ]
);
#[cfg(target_arch = "x86_64")]
assert_pair!(
    Avx2,
    Ifma,
    [
        VG_ED25519_KEY_PAIR_AVX2_IFMA_FEATURES,
        VG_ED25519_SIGN_EXPANDED_AVX2_IFMA_FEATURES,
        VG_ED25519_VERIFY_AVX2_IFMA_FEATURES
    ]
);

// Key derivation, signing and verification with SHA-512's `_sha3` need no
// CPU feature that its `select` does not require to choose it.
#[cfg(target_arch = "aarch64")]
const _: () = assert!(
    Sha512Backend::REQUIRES[Sha512Backend::Sha3 as usize].contains(Features::all(&[
        crate::arch::ed25519::VG_ED25519_KEY_PAIR_SHA3_FEATURES,
        crate::arch::ed25519::VG_ED25519_SIGN_EXPANDED_SHA3_FEATURES,
        crate::arch::ed25519::VG_ED25519_VERIFY_SHA3_FEATURES,
    ])),
    "an Ed25519 operation needs a CPU feature SHA-512's _sha3 is not chosen for"
);

/// An encoded Ed25519 public key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifyingKey {
    bytes: [u8; 32],
}

impl VerifyingKey {
    /// Import an encoded public key. Its encoding is checked during verification.
    pub fn from_bytes(bytes: &[u8; 32]) -> Self {
        Self { bytes: *bytes }
    }

    /// The encoded public key.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.bytes
    }

    /// Verify a pure Ed25519 signature (RFC 8032 §5.1.7).
    ///
    /// Public keys and signatures must use canonical encodings, and the
    /// signature scalar must be less than the subgroup order. This checks
    /// the uncofactored equation. The SHA-512 challenge is reduced modulo the
    /// subgroup order, following RFC 8032 §6. No additional subgroup or
    /// small-order rejection policy is imposed.
    /// Verification timing may depend on the public key, message, and signature.
    ///
    /// # Errors
    ///
    /// [`InvalidSignature`] if the signature is not 64 bytes long, an
    /// encoding is not canonical, or the equation does not hold.
    pub fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), InvalidSignature> {
        let dit = crate::dit::public(crate::dit::Why::Verify);
        let signature: &[u8; 64] = signature.try_into().map_err(|_| InvalidSignature)?;
        let valid = verify_message(dit, &self.bytes, message, signature);
        if valid == 1 {
            Ok(())
        } else {
            Err(InvalidSignature)
        }
    }
}

/// An Ed25519 signing key, storing its seed and derived public key.
///
/// The seed is cleared when the key is dropped. Debug output omits it.
#[derive(Clone)]
pub struct SigningKey {
    seed: [u8; 32],
    /// The seed's SHA-512 digest (RFC 8032 §5.1.6, step 1), which signing
    /// reads rather than hashing the seed again.
    expanded: [u8; 64],
    public: VerifyingKey,
}

impl core::fmt::Debug for SigningKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SigningKey").finish_non_exhaustive()
    }
}

impl Drop for SigningKey {
    fn drop(&mut self) {
        zeroize(&mut self.seed);
        zeroize(&mut self.expanded);
    }
}

impl SigningKey {
    /// Derive a signing key and its public key from an RFC 8032 seed.
    pub fn from_seed(seed: &[u8; 32]) -> Self {
        crate::dit::enter!(dit);
        let mut expanded = [0u8; 64];
        let mut public = [0u8; 32];
        key_pair(dit, &mut public, &mut expanded, seed);
        Self {
            seed: *seed,
            expanded,
            public: VerifyingKey { bytes: public },
        }
    }

    /// The original 32-byte seed.
    pub fn seed(&self) -> &[u8; 32] {
        &self.seed
    }

    /// The public key derived from this key's seed.
    pub fn verifying_key(&self) -> &VerifyingKey {
        &self.public
    }

    /// Sign `message` deterministically using pure Ed25519 (RFC 8032 §5.1.6).
    pub fn sign(&self, message: &[u8]) -> [u8; 64] {
        crate::dit::enter!(dit);
        sign_message(dit, self, message)
    }
}

/// The seed's SHA-512 digest (RFC 8032 §5.1.5, step 1) into `expanded` and
/// its public key (§5.1.5) into `public`, with the verified
/// `vg_ed25519_key_pair`.
fn key_pair(
    dit: crate::dit::Dit<'_>,
    public: &mut [u8; 32],
    expanded: &mut [u8; 64],
    seed: &[u8; 32],
) {
    let f = detected();
    let derive = match (Sha512Backend::select(f), Field::select(f)) {
        (Sha512Backend::Scalar, Field::Baseline) => vg_ed25519_key_pair,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Scalar, Field::Adx) => vg_ed25519_key_pair_adx,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Scalar, Field::Ifma) => vg_ed25519_key_pair_ifma,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::ShaNi, Field::Baseline) => vg_ed25519_key_pair_shani,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::ShaNi, Field::Adx) => vg_ed25519_key_pair_shani_adx,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::ShaNi, Field::Ifma) => vg_ed25519_key_pair_shani_ifma,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Avx2, Field::Baseline) => vg_ed25519_key_pair_avx2,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Avx2, Field::Adx) => vg_ed25519_key_pair_avx2_adx,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Avx2, Field::Ifma) => vg_ed25519_key_pair_avx2_ifma,
        #[cfg(target_arch = "aarch64")]
        (Sha512Backend::Sha3, Field::Baseline) => vg_ed25519_key_pair_sha3,
    };
    // Uninitialized: the contract holds whatever the scratch holds, so
    // filling it with zeros first would only cost time.
    let mut scratch = MaybeUninit::<[u64; 1024]>::uninit();
    // SAFETY: the public key, digest, seed and scratch are distinct objects
    // valid for 32, 64, 32 and 8192 bytes, respectively, so they overlap
    // neither each other nor the call's stack, and none wraps the address
    // space. The CPU has the features of both backends chosen (SHA-512's and
    // the field's).
    unsafe { derive(dit, public, expanded, seed, scratch.as_mut_ptr()) };
    // SAFETY: `scratch` is writable for its whole length.
    unsafe { zeroize_raw(scratch.as_mut_ptr().cast(), size_of::<[u64; 1024]>()) };
}

fn verify_message(
    dit: crate::dit::Dit<'_>,
    pk: &[u8; 32],
    message: &[u8],
    signature: &[u8; 64],
) -> u32 {
    let f = detected();
    let verify = match (Sha512Backend::select(f), Field::select(f)) {
        (Sha512Backend::Scalar, Field::Baseline) => vg_ed25519_verify,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Scalar, Field::Adx) => vg_ed25519_verify_adx,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Scalar, Field::Ifma) => vg_ed25519_verify_ifma,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::ShaNi, Field::Baseline) => vg_ed25519_verify_shani,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::ShaNi, Field::Adx) => vg_ed25519_verify_shani_adx,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::ShaNi, Field::Ifma) => vg_ed25519_verify_shani_ifma,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Avx2, Field::Baseline) => vg_ed25519_verify_avx2,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Avx2, Field::Adx) => vg_ed25519_verify_avx2_adx,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Avx2, Field::Ifma) => vg_ed25519_verify_avx2_ifma,
        #[cfg(target_arch = "aarch64")]
        (Sha512Backend::Sha3, Field::Baseline) => vg_ed25519_verify_sha3,
    };
    // Uninitialized: each function's contract holds whatever the scratch
    // holds, so filling it with zeros first would only cost time.
    let mut scratch = MaybeUninit::<[u64; 1024]>::uninit();
    // SAFETY: input references are valid for their declared lengths and scratch
    // is a distinct writable object. No object overlaps the call stack. The
    // CPU has the features of both backends chosen (SHA-512's and the
    // field's).
    let valid = unsafe {
        verify(
            dit,
            pk,
            message.as_ptr(),
            message.len(),
            signature,
            scratch.as_mut_ptr(),
        )
    };
    // SAFETY: `scratch` is writable for its whole length.
    unsafe { zeroize_raw(scratch.as_mut_ptr().cast(), size_of::<[u64; 1024]>()) };
    valid
}

fn sign_message(dit: crate::dit::Dit<'_>, key: &SigningKey, message: &[u8]) -> [u8; 64] {
    let f = detected();
    let sign = match (Sha512Backend::select(f), Field::select(f)) {
        (Sha512Backend::Scalar, Field::Baseline) => vg_ed25519_sign_expanded,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Scalar, Field::Adx) => vg_ed25519_sign_expanded_adx,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Scalar, Field::Ifma) => vg_ed25519_sign_expanded_ifma,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::ShaNi, Field::Baseline) => vg_ed25519_sign_expanded_shani,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::ShaNi, Field::Adx) => vg_ed25519_sign_expanded_shani_adx,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::ShaNi, Field::Ifma) => vg_ed25519_sign_expanded_shani_ifma,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Avx2, Field::Baseline) => vg_ed25519_sign_expanded_avx2,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Avx2, Field::Adx) => vg_ed25519_sign_expanded_avx2_adx,
        #[cfg(target_arch = "x86_64")]
        (Sha512Backend::Avx2, Field::Ifma) => vg_ed25519_sign_expanded_avx2_ifma,
        #[cfg(target_arch = "aarch64")]
        (Sha512Backend::Sha3, Field::Baseline) => vg_ed25519_sign_expanded_sha3,
    };
    let mut signature = [0u8; 64];
    // Uninitialized: each function's contract holds whatever the scratch
    // holds, so filling it with zeros first would only cost time.
    let mut scratch = MaybeUninit::<[u64; 1024]>::uninit();
    // SAFETY: the input references are valid for their declared lengths.
    // Signature and scratch are distinct writable objects, disjoint from the
    // inputs and the call's stack. None wraps the address space. `expanded`
    // and the public key are the seed's SHA-512 digest and public key: the
    // verified `vg_ed25519_key_pair` wrote both from the seed in `from_seed`,
    // and nothing changes them after. The CPU has the features of both
    // backends chosen (SHA-512's and the field's).
    unsafe {
        sign(
            dit,
            &mut signature,
            &key.expanded,
            &key.public.bytes,
            message.as_ptr(),
            message.len(),
            scratch.as_mut_ptr(),
        )
    };
    // SAFETY: `scratch` is writable for its whole length.
    unsafe { zeroize_raw(scratch.as_mut_ptr().cast(), size_of::<[u64; 1024]>()) };
    signature
}

#[cfg(all(test, target_arch = "x86_64"))]
mod x86_64_tests {
    use super::{
        Features, Field, Sha512Backend, VG_ED25519_SIGN_EXPANDED_IFMA_FEATURES,
        VG_ED25519_VERIFY_IFMA_FEATURES,
    };
    use crate::arch::ed25519::{
        VG_ED25519_SIGN_EXPANDED_AVX2_ADX_FEATURES, VG_ED25519_SIGN_EXPANDED_AVX2_FEATURES,
        VG_ED25519_SIGN_EXPANDED_AVX2_IFMA_FEATURES, VG_ED25519_SIGN_EXPANDED_SHANI_ADX_FEATURES,
        VG_ED25519_SIGN_EXPANDED_SHANI_FEATURES, VG_ED25519_SIGN_EXPANDED_SHANI_IFMA_FEATURES,
    };
    use verified_garbage_cpu::feature;

    /// The implementations chosen with exactly the features of each one,
    /// with only one of BMI2 and ADX, which `_adx` needs both of, with both
    /// but without the AVX2 `_adx` needs too, with all of `_ifma`'s but
    /// AVX512VL, and with verification's `_ifma` features alone, without the
    /// AVX512F of key derivation's and signing's.
    #[test]
    fn select() {
        let cases: [(Features, Sha512Backend, Field); 14] = [
            (Features(0), Sha512Backend::Scalar, Field::Baseline),
            (
                Features(feature::BMI2),
                Sha512Backend::Scalar,
                Field::Baseline,
            ),
            (
                Features(feature::ADX),
                Sha512Backend::Scalar,
                Field::Baseline,
            ),
            (
                Features(feature::BMI2 | feature::ADX),
                Sha512Backend::Scalar,
                Field::Baseline,
            ),
            (
                Features(feature::AVX | feature::AVX2 | feature::BMI2 | feature::ADX),
                Sha512Backend::Scalar,
                Field::Adx,
            ),
            (
                VG_ED25519_SIGN_EXPANDED_AVX2_FEATURES,
                Sha512Backend::Avx2,
                Field::Baseline,
            ),
            (
                VG_ED25519_SIGN_EXPANDED_AVX2_ADX_FEATURES,
                Sha512Backend::Avx2,
                Field::Adx,
            ),
            (
                VG_ED25519_SIGN_EXPANDED_SHANI_FEATURES,
                Sha512Backend::ShaNi,
                Field::Baseline,
            ),
            (
                VG_ED25519_SIGN_EXPANDED_SHANI_ADX_FEATURES,
                Sha512Backend::ShaNi,
                Field::Adx,
            ),
            (
                VG_ED25519_SIGN_EXPANDED_IFMA_FEATURES,
                Sha512Backend::Scalar,
                Field::Ifma,
            ),
            (
                Features(
                    feature::AVX
                        | feature::AVX2
                        | feature::BMI2
                        | feature::ADX
                        | feature::AVX512F
                        | feature::AVX512IFMA,
                ),
                Sha512Backend::Scalar,
                Field::Adx,
            ),
            (
                VG_ED25519_VERIFY_IFMA_FEATURES,
                Sha512Backend::Scalar,
                Field::Adx,
            ),
            (
                VG_ED25519_SIGN_EXPANDED_AVX2_IFMA_FEATURES,
                Sha512Backend::Avx2,
                Field::Ifma,
            ),
            (
                VG_ED25519_SIGN_EXPANDED_SHANI_IFMA_FEATURES,
                Sha512Backend::ShaNi,
                Field::Ifma,
            ),
        ];
        for (features, s, f) in cases {
            let chosen = (Sha512Backend::select(features), Field::select(features));
            assert_eq!(chosen, (s, f), "{features:?}");
        }
    }
}
