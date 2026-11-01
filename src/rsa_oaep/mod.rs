//! RSAES-OAEP encryption and decryption (RFC 8017 §7.1).
//!
//! [`encrypt`] is the verified `vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed`
//! (contract `VG.Spec.RsaOaep.encryptPrecomputedContract`), with a seed from
//! the operating system's generator; it encrypts the encoded message with
//! `vg_rsa_public_precomputed_checked`, reusing the public key's precomputed
//! modulus values (on x86-64, with ADX multiplication when available).
//!
//! [`decrypt`] is the verified `vg_rsa_oaep_<H>_mgf1_<G>_decrypt` (contract
//! `VG.Spec.RsaOaep.decryptContract`), which computes the encoded message
//! with `vg_rsa_private_checked`, as [`PrivateKey::private_op`] does, then
//! decodes it in constant time: whether the decoding succeeds, where the
//! message starts and its length do not affect the timing of the verified
//! function, and every failure (of the ciphertext, not below the modulus,
//! or of its decoding) is the one error [`Error::Decryption`]. The message
//! is returned, and with it its length.
//!
//! The hash functions are any of SHA-1, SHA-224, SHA-256, SHA-384,
//! SHA-512, SHA-512/224 and SHA-512/256, with MGF1 over the same hash
//! function or over SHA-1 (the pairs in use, and those Wycheproof tests);
//! other pairs are refused ([`Error::UnsupportedHash`]). On an x86-64 CPU
//! with the SHA extensions or AVX2, and with BMI2, ADX and AVX2 (and
//! AVX512_IFMA), and on an AArch64 CPU with the SHA-2 or SHA-3
//! instructions, it uses the faster compression functions and private-key
//! operations, as [`hashes`](crate::hashes) and [`rsa`](crate::rsa) do.
//! Each pair has a file, `<H>_mgf1_<G>.rs`, naming its verified functions
//! for each choice of those implementations (`oaep_pair!`).
//!
//! This module only checks the lengths, draws the seed and allocates the
//! memory the functions work in.

#![cfg(all(
    any(
        target_arch = "x86",
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64"
    ),
    feature = "alloc"
))]

mod sha1_mgf1_sha1;
mod sha224_mgf1_sha1;
mod sha224_mgf1_sha224;
mod sha256_mgf1_sha1;
mod sha256_mgf1_sha256;
mod sha384_mgf1_sha1;
mod sha384_mgf1_sha384;
mod sha512_224_mgf1_sha1;
mod sha512_224_mgf1_sha512_224;
mod sha512_256_mgf1_sha1;
mod sha512_256_mgf1_sha512_256;
mod sha512_mgf1_sha1;
mod sha512_mgf1_sha512;

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use crate::cpu::detected;
use crate::rsa::{PrivateKey, PublicKey};
pub use crate::rsa_pkcs1_sig::Hash;
use crate::rsa_pss::{public_scratch_words, scratch_words};
use crate::zeroize::zeroize;

/// Why an encryption or a decryption was refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The pair of hash functions is not one this module supports.
    UnsupportedHash,
    /// The message is longer than the modulus' length less twice the hash
    /// function's length, less 2.
    MessageTooLong,
    /// The ciphertext is not as long as the modulus.
    InvalidLength,
    /// The ciphertext is not below the modulus, or does not decrypt to a
    /// valid encoded message for the label: which is not told.
    Decryption,
    /// The private-key operation's result failed its check against the
    /// public exponent (see [`rsa::Error::Fault`](crate::rsa::Error::Fault)).
    Fault,
    /// The operating system's random number generator failed.
    Randomness,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::UnsupportedHash => "unsupported pair of hash functions for RSA OAEP",
            Error::MessageTooLong => "RSA OAEP message too long for the modulus",
            Error::InvalidLength => "RSA ciphertext length is not the modulus length",
            Error::Decryption => "RSA OAEP decryption failed",
            Error::Fault => {
                "RSA private-key operation failed its check against the public exponent"
            }
            Error::Randomness => "the random number generator failed",
        })
    }
}

impl core::error::Error for Error {}

/// The operating system's random bytes.
fn os_random(buf: &mut [u8]) -> Result<(), Error> {
    getrandom::fill(buf).map_err(|_| Error::Randomness)
}

/// Declares the types of verified functions, in the calling convention the
/// emitter generates on each target: `sysv64` on x86-64 (on Windows too),
/// and C's on x86, AArch64 and ARMv7.
macro_rules! verified_fn_types {
    ($(
        $(#[$doc:meta])*
        type $name:ident $(<const $l:ident: usize>)? = fn($($arg:ty),* $(,)?) -> $ret:ty;
    )*) => {$(
        $(#[$doc])*
        #[cfg(target_arch = "x86_64")]
        type $name $(<const $l: usize>)? = unsafe extern "sysv64" fn($($arg),*) -> $ret;
        $(#[$doc])*
        #[cfg(any(target_arch = "x86", target_arch = "aarch64", target_arch = "arm", target_arch = "powerpc64"))]
        type $name $(<const $l: usize>)? = unsafe extern "C" fn($($arg),*) -> $ret;
    )*};
}

verified_fn_types! {
    /// The type of the implementations of
    /// `vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed`, for `H` of `L` bytes.
    type EncryptFn<const L: usize> = fn(
        *mut u8,
        usize,
        *const u8,
        usize,
        *const u8,
        usize,
        *const u8,
        usize,
        *const u8,
        usize,
        *const [u8; L],
        *mut u64,
        usize,
        *const u64,
        usize,
    ) -> u32;

    /// The type of the implementations of `vg_rsa_oaep_<H>_mgf1_<G>_decrypt`.
    type DecryptFn = fn(
        *mut u8,
        usize,
        *mut [u64; 1],
        *const u8,
        usize,
        *const u8,
        usize,
        *const u8,
        usize,
        *const u8,
        usize,
        *const u8,
        usize,
        *const u8,
        usize,
        *const u8,
        usize,
        *const u8,
        usize,
        *const u8,
        usize,
        *mut u64,
        usize,
    ) -> u32;
}

/// `Some($body)`, with `$fns` the verified functions (`(encrypt, decrypt)`)
/// of the hash function `$hash` with MGF1 over `$mgf1` for the
/// implementations this CPU runs best, or `None` if this module does not
/// support the pair.
macro_rules! with_functions {
    (@pairs $pair:expr, |$fns:ident| $body:expr, {$(($h:ident, $g:ident) => $module:ident),* $(,)?}) => {{
        let f = detected();
        match $pair {
            $((Hash::$h, Hash::$g) => {
                let $fns = $module::functions(f);
                Some($body)
            })*
            _ => None,
        }
    }};
    ($hash:expr, $mgf1:expr, |$fns:ident| $body:expr) => {
        with_functions!(@pairs ($hash, $mgf1), |$fns| $body, {
            (Sha1, Sha1) => sha1_mgf1_sha1,
            (Sha224, Sha1) => sha224_mgf1_sha1,
            (Sha224, Sha224) => sha224_mgf1_sha224,
            (Sha256, Sha1) => sha256_mgf1_sha1,
            (Sha256, Sha256) => sha256_mgf1_sha256,
            (Sha384, Sha1) => sha384_mgf1_sha1,
            (Sha384, Sha384) => sha384_mgf1_sha384,
            (Sha512, Sha1) => sha512_mgf1_sha1,
            (Sha512, Sha512) => sha512_mgf1_sha512,
            (Sha512_224, Sha1) => sha512_224_mgf1_sha1,
            (Sha512_224, Sha512_224) => sha512_224_mgf1_sha512_224,
            (Sha512_256, Sha1) => sha512_256_mgf1_sha1,
            (Sha512_256, Sha512_256) => sha512_256_mgf1_sha512_256,
        })
    };
}

/// RSAES-OAEP-ENCRYPT (RFC 8017 §7.1.1) with the hash function `hash` and
/// MGF1 over `mgf1_hash`: encrypts `plaintext`, of at most
/// [`modulus_len`](PublicKey::modulus_len)` - 2 hLen - 2` bytes, with `key`
/// and the label `label`, with a random seed, and returns the ciphertext
/// ([`modulus_len`](PublicKey::modulus_len) bytes, big-endian). The timing
/// may depend on the public key and the lengths of the plaintext and the
/// label, not on their contents.
///
/// Repeated operations with the same key reuse its scratch allocation,
/// shared with signature verification. The buffer is wiped before reuse;
/// concurrent callers use independent buffers.
pub fn encrypt(
    key: &PublicKey,
    plaintext: &[u8],
    hash: Hash,
    mgf1_hash: Hash,
    label: &[u8],
) -> Result<Vec<u8>, Error> {
    encrypt_with_rng(key, plaintext, hash, mgf1_hash, label, os_random)
}

/// [`encrypt`], with its seed drawn from `random` instead of the operating
/// system.
///
/// Not part of the API: it lets benchmarks compare implementations on
/// identical work, from fixed tapes. The ciphertext is secure only if
/// `random` supplies uniformly random bytes, never reused.
#[doc(hidden)]
pub fn encrypt_with_rng(
    key: &PublicKey,
    plaintext: &[u8],
    hash: Hash,
    mgf1_hash: Hash,
    label: &[u8],
    random: impl FnMut(&mut [u8]) -> Result<(), Error>,
) -> Result<Vec<u8>, Error> {
    with_functions!(hash, mgf1_hash, |fns| encrypt_with(
        key, plaintext, label, fns.0, random
    ))
    .unwrap_or(Err(Error::UnsupportedHash))
}

/// `f`, a `vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed` that this CPU can
/// run, with a seed from `random`.
fn encrypt_with<const L: usize>(
    key: &PublicKey,
    plaintext: &[u8],
    label: &[u8],
    f: EncryptFn<L>,
    mut random: impl FnMut(&mut [u8]) -> Result<(), Error>,
) -> Result<Vec<u8>, Error> {
    let k = key.modulus_len();
    if plaintext.len() + 2 * L + 2 > k {
        return Err(Error::MessageTooLong);
    }
    let mut seed = [0u8; L];
    random(&mut seed)?;
    let mut out = vec![0u8; k];
    let mut scratch = key.verify_scratch.take(public_scratch_words(k), true);
    let pre = key.pre(&mut scratch);
    // SAFETY: each pointer is valid for its length (`out` and `scratch` for
    // writes, `seed` for `L` bytes, the hash function's length), and none
    // overlaps another or wraps around, as they are distinct Rust
    // allocations; `PublicKey::new` gives `64 ≤ n_len ≤ 1024`,
    // `1 ≤ e_len ≤ 5 ≤ n_len`, and `out_len = n_len` and
    // `scratch_len = 8 ⌈n_len / 8⌉ + 1072`; `pre` holds the verified
    // precomputation for `key.n`, with `2 * ceil(n_len / 8)` words; and the
    // CPU has the features of `f`, which `functions` chose for the features
    // detected (its `backend_features` test checks that they need no others).
    let r = unsafe {
        f(
            out.as_mut_ptr(),
            k,
            key.n.as_ptr(),
            k,
            key.e.as_ptr(),
            key.e.len(),
            label.as_ptr(),
            label.len(),
            plaintext.as_ptr(),
            plaintext.len(),
            &seed,
            scratch.as_mut_ptr(),
            scratch.len(),
            pre.as_ptr(),
            pre.len(),
        )
    };
    // ScratchLease wipes the encoded message and its powers before reuse.
    zeroize(&mut seed);
    // `PublicKey::new` checked `n`, and the message's length is checked
    // above.
    assert_eq!(r, 1, "OAEP encryption refused a valid key and message");
    Ok(out)
}

/// RSAES-OAEP-DECRYPT (RFC 8017 §7.1.2) with the hash function `hash` and
/// MGF1 over `mgf1_hash`: decrypts `ciphertext`
/// ([`modulus_len`](PrivateKey::modulus_len) bytes, big-endian) with `key`
/// and the label `label`, and returns the message. A ciphertext not below
/// the modulus and every failure of its decoding are the one error
/// [`Error::Decryption`]. The timing may depend on the public key, the
/// lengths of the primes and of the label, not on the ciphertext, the
/// private key, the label's contents, whether the decryption succeeds or
/// the message's length.
pub fn decrypt(
    key: &PrivateKey,
    ciphertext: &[u8],
    hash: Hash,
    mgf1_hash: Hash,
    label: &[u8],
) -> Result<Vec<u8>, Error> {
    with_functions!(hash, mgf1_hash, |fns| decrypt_with(
        key, ciphertext, label, fns.1
    ))
    .unwrap_or(Err(Error::UnsupportedHash))
}

/// `f`, a `vg_rsa_oaep_<H>_mgf1_<G>_decrypt` that this CPU can run.
fn decrypt_with(
    key: &PrivateKey,
    ciphertext: &[u8],
    label: &[u8],
    f: DecryptFn,
) -> Result<Vec<u8>, Error> {
    let k = key.modulus_len();
    if ciphertext.len() != k {
        return Err(Error::InvalidLength);
    }
    let mut out = vec![0u8; k];
    let mut len = [0u64; 1];
    let mut scratch = crate::rsa::Scratch::new(scratch_words(k));
    // SAFETY: each pointer is valid for its length (`out`, `len` and
    // `scratch` for writes), and none overlaps another or wraps around, as
    // they are distinct Rust allocations; `PrivateKey::from_crt` and the
    // check above give `64 ≤ n_len ≤ 1024`, `out_len = ct_len = n_len`,
    // `1 ≤ e_len ≤ 5 ≤ n_len`, `1 ≤ p_len < n_len`, `1 ≤ q_len < n_len`,
    // `dp_len = qinv_len = p_len`, `dq_len = q_len` and
    // `scratch_len = 16 n_len + 1056`; and the CPU has the features of `f`,
    // which `functions` chose for the features detected (its
    // `backend_features` test checks that they need no others).
    let r = unsafe {
        f(
            out.as_mut_ptr(),
            k,
            &mut len,
            key.n.as_ptr(),
            k,
            key.e.as_ptr(),
            key.e.len(),
            key.p.as_ptr(),
            key.p.len(),
            key.q.as_ptr(),
            key.q.len(),
            key.dp.as_ptr(),
            key.dp.len(),
            key.dq.as_ptr(),
            key.dq.len(),
            key.qinv.as_ptr(),
            key.qinv.len(),
            label.as_ptr(),
            label.len(),
            ciphertext.as_ptr(),
            k,
            scratch.as_mut_ptr(),
            scratch.len(),
        )
    };
    match r {
        1 => {
            // The message is at most `n_len - 2 hLen - 2` bytes.
            out.truncate(len[0] as usize);
            Ok(out)
        }
        2 => Err(Error::Fault),
        _ => Err(Error::Decryption),
    }
}

/// The verified functions of one pair of hash functions, `H`, of `$n`-byte
/// values, and `G`, MGF1's: `functions`, which chooses, for a CPU with the
/// features `f`, the implementations of their compression functions it runs
/// best (the variants of their streaming backends: `$h`'s, and `$g`'s for
/// MGF1 over another hash function) and of the RSA operations
/// (`crate::rsa::Backend`), and returns encryption and decryption calling
/// them; and a test that each needs no CPU feature that was not required to
/// choose it.
///
/// Each arm names, for one choice of the hash functions' implementations,
/// encryption and decryption calling RSA's baseline code, each with the
/// generated constants of the CPU features it needs (none for the baseline
/// ISA's), and, for the arms that have them, used on x86-64 only, those
/// calling its other RSA backends: `encrypt_adx`, `encrypt_ifma`,
/// `decrypt_adx` and `decrypt_ifma`; and, used on ARMv7 only, decryption
/// calling the private-key operation with `umaal`, `decrypt_umaal`
/// and encryption through its UMAAL public operation, `encrypt_umaal`.
/// With MGF1 over another hash function, the arms after `never` are the
/// pairs of implementations no CPU chooses: they are there for the match to
/// be exhaustive, and the test checks that no set of features chooses them.
macro_rules! oaep_pair {
    (@impl $f:ident, $n:literal, $select:expr,
        [$([$(#[$attr:meta])*] $pat:pat => $fns:tt)*],
        [$([$(#[$nattr:meta])*] $npat:pat => $nfns:tt)*]
    ) => {
        /// The length of the hash function's values.
        const N: usize = $n;

        /// The functions, `(encrypt, decrypt)`, for the implementations
        /// that a CPU with the features `f` runs best.
        pub(super) fn functions(
            $f: verified_garbage_cpu::Features,
        ) -> (super::EncryptFn<N>, super::DecryptFn) {
            let rsa = $crate::rsa::Backend::select($f);
            match $select {
                $($(#[$attr])* $pat => $crate::rsa_oaep::oaep_pair!(@fns rsa, $fns),)*
                // NO-COVERAGE-START
                $($(#[$nattr])* $npat => $crate::rsa_oaep::oaep_pair!(@fns rsa, $nfns),)*
                // NO-COVERAGE-END
            }
        }

        #[cfg(test)]
        mod tests {
            use super::*;

            /// Each function needs no CPU feature that the implementations
            /// it calls were not chosen for, and no set of features chooses
            /// the arms after `never`: on every set of features.
            #[test]
            fn backend_features() {
                for bits in 0..1u32 << $crate::cpu::NAMES.len() {
                    let $f = verified_garbage_cpu::Features(bits);
                    let rsa = $crate::rsa::Backend::select($f);
                    let (encrypt, decrypt) = match $select {
                        $($(#[$attr])* $pat => $crate::rsa_oaep::oaep_pair!(@features rsa, $fns),)*
                        // NO-COVERAGE-START
                        $($(#[$nattr])* $npat => panic!("{} chosen for {bits:#b}", stringify!($npat)),)*
                        // NO-COVERAGE-END
                    };
                    assert!($f.contains(encrypt) && $f.contains(decrypt), "{bits:#b}");
                }
            }
        }
    };
    (@fns $rsa:ident, {
        encrypt: $enc:path [$($ereq:path),*],
        decrypt: $dec:path [$($dreq:path),*]
        $(,
            encrypt_adx: $enc_adx:path [$($eareq:path),*],
            encrypt_ifma: $enc_ifma:path [$($eireq:path),*],
            decrypt_adx: $dec_adx:path [$($dareq:path),*],
            decrypt_ifma: $dec_ifma:path [$($direq:path),*]
        )?
        $(,
            decrypt_umaal: $dec_umaal:path [$($dureq:path),*],
            encrypt_umaal: $enc_umaal:path [$($eureq:path),*]
        )? $(,)?
    }) => {
        (
            match $rsa {
                $crate::rsa::Backend::Baseline => $enc,
                $(
                    #[cfg(target_arch = "x86_64")]
                    $crate::rsa::Backend::Adx => $enc_adx,
                    #[cfg(target_arch = "x86_64")]
                    $crate::rsa::Backend::Ifma => $enc_ifma,
                )?
                $(
                    #[cfg(all(
                        target_arch = "arm",
                        any(
                            target_os = "linux",
                            target_os = "android",
                            target_os = "freebsd",
                            target_os = "netbsd",
                            target_os = "openbsd"
                        )
                    ))]
                    $crate::rsa::Backend::Umaal => $enc_umaal,
                )?
            },
            match $rsa {
                $crate::rsa::Backend::Baseline => $dec,
                $(
                    #[cfg(target_arch = "x86_64")]
                    $crate::rsa::Backend::Adx => $dec_adx,
                    #[cfg(target_arch = "x86_64")]
                    $crate::rsa::Backend::Ifma => $dec_ifma,
                )?
                $(
                    #[cfg(all(
                        target_arch = "arm",
                        any(
                            target_os = "linux",
                            target_os = "android",
                            target_os = "freebsd",
                            target_os = "netbsd",
                            target_os = "openbsd"
                        )
                    ))]
                    $crate::rsa::Backend::Umaal => $dec_umaal,
                )?
            },
        )
    };
    (@features $rsa:ident, {
        encrypt: $enc:path [$($ereq:path),*],
        decrypt: $dec:path [$($dreq:path),*]
        $(,
            encrypt_adx: $enc_adx:path [$($eareq:path),*],
            encrypt_ifma: $enc_ifma:path [$($eireq:path),*],
            decrypt_adx: $dec_adx:path [$($dareq:path),*],
            decrypt_ifma: $dec_ifma:path [$($direq:path),*]
        )?
        $(,
            decrypt_umaal: $dec_umaal:path [$($dureq:path),*],
            encrypt_umaal: $enc_umaal:path [$($eureq:path),*]
        )? $(,)?
    }) => {
        (
            match $rsa {
                $crate::rsa::Backend::Baseline => verified_garbage_cpu::Features::all(&[$($ereq),*]),
                $(
                    #[cfg(target_arch = "x86_64")]
                    $crate::rsa::Backend::Adx => verified_garbage_cpu::Features::all(&[$($eareq),*]),
                    #[cfg(target_arch = "x86_64")]
                    $crate::rsa::Backend::Ifma => verified_garbage_cpu::Features::all(&[$($eireq),*]),
                )?
                $(
                    #[cfg(all(
                        target_arch = "arm",
                        any(
                            target_os = "linux",
                            target_os = "android",
                            target_os = "freebsd",
                            target_os = "netbsd",
                            target_os = "openbsd"
                        )
                    ))]
                    $crate::rsa::Backend::Umaal => verified_garbage_cpu::Features::all(&[$($eureq),*]),
                )?
            },
            match $rsa {
                $crate::rsa::Backend::Baseline => verified_garbage_cpu::Features::all(&[$($dreq),*]),
                $(
                    #[cfg(target_arch = "x86_64")]
                    $crate::rsa::Backend::Adx => verified_garbage_cpu::Features::all(&[$($dareq),*]),
                    #[cfg(target_arch = "x86_64")]
                    $crate::rsa::Backend::Ifma => verified_garbage_cpu::Features::all(&[$($direq),*]),
                )?
                $(
                    #[cfg(all(
                        target_arch = "arm",
                        any(
                            target_os = "linux",
                            target_os = "android",
                            target_os = "freebsd",
                            target_os = "netbsd",
                            target_os = "openbsd"
                        )
                    ))]
                    $crate::rsa::Backend::Umaal => verified_garbage_cpu::Features::all(&[$($dureq),*]),
                )?
            },
        )
    };
    // MGF1 over the hash function itself: its backend chooses both.
    ($n:literal, $h:ident {
        $($(#[$attr:meta])* $hv:ident => $fns:tt),* $(,)?
    }) => {
        $crate::rsa_oaep::oaep_pair!(@impl f, $n, $h::select(f),
            [$([$(#[$attr])*] $h::$hv => $fns)*], []);
    };
    // MGF1 over another hash function: the two backends choose.
    ($n:literal, $h:ident, $g:ident {
        $($(#[$attr:meta])* ($hv:ident, $gv:ident) => $fns:tt),* $(,)?
    } never {
        $($(#[$nattr:meta])* ($nhv:ident, $ngv:ident) => $nfns:tt),* $(,)?
    }) => {
        $crate::rsa_oaep::oaep_pair!(@impl f, $n, ($h::select(f), $g::select(f)),
            [$([$(#[$attr])*] ($h::$hv, $g::$gv) => $fns)*],
            [$([$(#[$nattr])*] ($h::$nhv, $g::$ngv) => $nfns)*]);
    };
}

use oaep_pair;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rsa::tests::composite_key;
    use alloc::string::ToString;

    #[test]
    fn pairs() {
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
            for g in all {
                let ok = h != Hash::Md5
                    && !matches!(
                        h,
                        Hash::Sha3_224 | Hash::Sha3_256 | Hash::Sha3_384 | Hash::Sha3_512
                    )
                    && (g == h || g == Hash::Sha1);
                assert_eq!(with_functions!(h, g, |_fns| ()).is_some(), ok);
                n += usize::from(ok);
            }
        }
        assert_eq!(n, 13);
    }

    #[test]
    fn refused() {
        let (private, public) = composite_key();
        assert_eq!(
            encrypt(&public, b"", Hash::Md5, Hash::Md5, b""),
            Err(Error::UnsupportedHash)
        );
        assert_eq!(
            decrypt(&private, &[0; 64], Hash::Sha256, Hash::Sha224, b""),
            Err(Error::UnsupportedHash)
        );
        // 64 bytes hold at most 22 bytes of message with SHA-1, none with
        // SHA-512.
        assert_eq!(
            encrypt(&public, &[0; 23], Hash::Sha1, Hash::Sha1, b""),
            Err(Error::MessageTooLong)
        );
        assert_eq!(
            encrypt(&public, b"", Hash::Sha512, Hash::Sha512, b""),
            Err(Error::MessageTooLong)
        );
        let c = encrypt(&public, &[7; 22], Hash::Sha1, Hash::Sha1, b"label").unwrap();
        assert_eq!(c.len(), 64);
        assert_eq!(
            decrypt(&private, &c[1..], Hash::Sha1, Hash::Sha1, b"label"),
            Err(Error::InvalidLength)
        );
        let mut two = vec![0; 64];
        two[63] = 2;
        assert_eq!(
            decrypt(&private, &two, Hash::Sha1, Hash::Sha1, b""),
            Err(Error::Fault)
        );
        // Not below the modulus.
        assert_eq!(
            decrypt(&private, &[0xff; 64], Hash::Sha1, Hash::Sha1, b""),
            Err(Error::Decryption)
        );
    }

    /// The same seed gives the same ciphertext, as the fixed-tape benchmark
    /// relies on, and a failing draw fails the encryption.
    #[test]
    fn encryption_from_a_fixed_tape_is_deterministic() {
        let (_, public) = composite_key();
        let encrypt = |byte| {
            encrypt_with_rng(&public, &[7; 22], Hash::Sha1, Hash::Sha1, b"", |buf| {
                buf.fill(byte);
                Ok(())
            })
        };
        assert_eq!(encrypt(1), encrypt(1));
        assert_ne!(encrypt(1), encrypt(2));
        assert_eq!(
            encrypt_with_rng(&public, b"", Hash::Sha1, Hash::Sha1, b"", |_| {
                Err(Error::Randomness)
            }),
            Err(Error::Randomness)
        );
    }

    #[test]
    fn errors_display() {
        for e in [
            Error::UnsupportedHash,
            Error::MessageTooLong,
            Error::InvalidLength,
            Error::Decryption,
            Error::Fault,
            Error::Randomness,
        ] {
            assert!(!e.to_string().is_empty());
        }
    }
}
