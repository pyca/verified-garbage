//! RSAES-OAEP encryption and decryption (RFC 8017 §7.1).
//!
//! [`encrypt`] is the verified encryption with a precomputed public key,
//! with a seed from the operating system's generator; it encrypts the
//! encoded message with `vg_rsa_public_precomputed_checked`, reusing the
//! public key's precomputed modulus values (on x86-64, with ADX
//! multiplication when available).
//!
//! [`decrypt`] is the verified decryption, which computes the encoded
//! message with `vg_rsa_private_checked`, as [`PrivateKey::private_op`]
//! does, then decodes it in constant time: whether the decoding succeeds,
//! where the message starts and its length do not affect the timing of the
//! verified function, and every failure (of the ciphertext, not below the
//! modulus, or of its decoding) is the one error [`Error::Decryption`]. The
//! message is returned, and with it its length.
//!
//! On x86-64 they are `vg_rsa_oaep_encrypt_precomputed` and
//! `vg_rsa_oaep_decrypt` (contracts `VG.Spec.RsaOaep.encryptAnyContract`
//! and `decryptAnyContract`, `any.rs`), which take the hash functions as
//! tables of their streaming functions (`crate::hash_fns`): any of SHA-1,
//! SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and SHA-512/256, for the
//! label's hash and for MGF1. On AArch64 they are
//! `vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed` and
//! `vg_rsa_oaep_<H>_mgf1_<G>_decrypt` (contracts
//! `VG.Spec.RsaOaep.encryptPrecomputedContract` and `decryptContract`), for
//! the same hash functions with MGF1 over the same hash function or over
//! SHA-1 (the pairs in use, and those Wycheproof tests); each pair has a
//! file, `<H>_mgf1_<G>.rs`, naming its verified functions for each choice
//! of the implementations of its compression functions (`oaep_pair!`).
//! Other hash functions are refused ([`Error::UnsupportedHash`]). On an
//! x86-64 CPU with the SHA extensions or AVX2, and with BMI2, ADX and AVX2
//! (and AVX512_IFMA), and on an AArch64 CPU with the SHA-2 or SHA-3
//! instructions, it uses the faster compression functions and private-key
//! operations, as [`hashes`](crate::hashes) and [`rsa`](crate::rsa) do.
//!
//! This module only checks the lengths, draws the seed and allocates the
//! memory the functions work in.

#![cfg(all(
    any(target_arch = "x86_64", target_arch = "aarch64"),
    feature = "alloc"
))]

mod any;
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

#[cfg(target_arch = "aarch64")]
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

/// The type of the implementations of
/// `vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed`, for `H` of `L` bytes.
#[cfg(target_arch = "aarch64")]
type EncryptFn<const L: usize> = unsafe extern "C" fn(
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
#[cfg(target_arch = "aarch64")]
type DecryptFn = unsafe extern "C" fn(
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

/// `Some($body)`, with `$fns` the verified functions (`(encrypt, decrypt)`)
/// of the hash function `$hash` with MGF1 over `$mgf1` for the
/// implementations this CPU runs best, or `None` if this module does not
/// support the pair.
#[cfg(target_arch = "aarch64")]
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
    #[cfg(target_arch = "x86_64")]
    return any::encrypt(key, plaintext, hash, mgf1_hash, label);
    #[cfg(target_arch = "aarch64")]
    with_functions!(hash, mgf1_hash, |fns| encrypt_with(
        key,
        plaintext,
        hash.digest_len(),
        |out, seed, scratch, pre| {
            // SAFETY: `encrypt_with`'s, and `seed` holds `L` bytes, the
            // length of `hash`'s values; the CPU has the features of the
            // function, which `functions` chose for the features detected
            // (its `backend_features` test checks that they need no others).
            unsafe {
                (fns.0)(
                    out.as_mut_ptr(),
                    out.len(),
                    key.n.as_ptr(),
                    key.n.len(),
                    key.e.as_ptr(),
                    key.e.len(),
                    label.as_ptr(),
                    label.len(),
                    plaintext.as_ptr(),
                    plaintext.len(),
                    seed.as_ptr().cast(),
                    scratch.as_mut_ptr(),
                    scratch.len(),
                    pre.as_ptr(),
                    pre.len(),
                )
            }
        }
    ))
    .unwrap_or(Err(Error::UnsupportedHash))
}

/// Encryption with a random seed of `h_len` bytes, by `f(out, seed,
/// scratch, pre)`, a verified encryption of `plaintext` with `key` (and a
/// label and the hash functions it was chosen for, of `h_len`-byte values)
/// that this CPU can run.
///
/// `f` may assume that each of its pointers is valid for its length (`out`
/// and `scratch` for writes), and none overlaps another or wraps around, as
/// they are distinct Rust allocations; that `PublicKey::new` gives
/// `64 ≤ n_len ≤ 1024` and `1 ≤ e_len ≤ 5 ≤ n_len`; that `out_len = n_len`,
/// `seed_len = h_len` and `scratch_len = 8 ⌈n_len / 8⌉ + 1072`; and that
/// `pre` holds the verified precomputation for `key.n`, with
/// `2 * ceil(n_len / 8)` words.
fn encrypt_with(
    key: &PublicKey,
    plaintext: &[u8],
    h_len: usize,
    f: impl FnOnce(&mut [u8], &[u8], &mut [u64], &[u64]) -> u32,
) -> Result<Vec<u8>, Error> {
    let k = key.modulus_len();
    if plaintext.len() + 2 * h_len + 2 > k {
        return Err(Error::MessageTooLong);
    }
    let mut seed = [0u8; 64];
    let seed = &mut seed[..h_len];
    os_random(seed)?;
    let mut out = vec![0u8; k];
    let mut scratch = key.verify_scratch.take(public_scratch_words(k), true);
    let pre = key.pre(&mut scratch);
    let r = f(&mut out, seed, &mut scratch, pre);
    // ScratchLease wipes the encoded message and its powers before reuse.
    zeroize(seed);
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
    #[cfg(target_arch = "x86_64")]
    return any::decrypt(key, ciphertext, hash, mgf1_hash, label);
    #[cfg(target_arch = "aarch64")]
    with_functions!(hash, mgf1_hash, |fns| decrypt_with(
        key,
        ciphertext,
        |out, len, scratch| {
            // SAFETY: `decrypt_with`'s; the CPU has the features of the
            // function, which `functions` chose for the features detected
            // (its `backend_features` test checks that they need no others).
            unsafe {
                (fns.1)(
                    out.as_mut_ptr(),
                    out.len(),
                    len,
                    key.n.as_ptr(),
                    key.n.len(),
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
                    ciphertext.len(),
                    scratch.as_mut_ptr(),
                    scratch.len(),
                )
            }
        }
    ))
    .unwrap_or(Err(Error::UnsupportedHash))
}

/// Decryption of `ciphertext` by `f(out, msg_len, scratch)`, a verified
/// decryption with `key` (and a label and the hash functions it was chosen
/// for) that this CPU can run.
///
/// `f` may assume that each of its pointers is valid for its length (`out`,
/// `msg_len` and `scratch` for writes), and none overlaps another or wraps
/// around, as they are distinct Rust allocations; and that
/// `PrivateKey::from_crt` and the check here give `64 ≤ n_len ≤ 1024`,
/// `out_len = ct_len = n_len`, `1 ≤ e_len ≤ 5 ≤ n_len`, `1 ≤ p_len < n_len`,
/// `1 ≤ q_len < n_len`, `dp_len = qinv_len = p_len`, `dq_len = q_len` and
/// `scratch_len = 16 n_len + 1056`.
fn decrypt_with(
    key: &PrivateKey,
    ciphertext: &[u8],
    f: impl FnOnce(&mut [u8], &mut [u64; 1], &mut [u64]) -> u32,
) -> Result<Vec<u8>, Error> {
    let k = key.modulus_len();
    if ciphertext.len() != k {
        return Err(Error::InvalidLength);
    }
    let mut out = vec![0u8; k];
    let mut len = [0u64; 1];
    let mut scratch = crate::rsa::Scratch::new(scratch_words(k));
    match f(&mut out, &mut len, &mut scratch) {
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
/// MGF1 over another hash function), and returns encryption and decryption
/// calling them; and a test that each needs no CPU feature that was not
/// required to choose it.
///
/// Each arm names, for one choice of the hash functions' implementations,
/// encryption and decryption, each with the generated constants of the CPU
/// features it needs (none for the baseline ISA's).
/// With MGF1 over another hash function, the arms after `never` are the
/// pairs of implementations no CPU chooses: they are there for the match to
/// be exhaustive, and the test checks that no set of features chooses them.
#[cfg(target_arch = "aarch64")]
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
            $f: $crate::cpu::Features,
        ) -> (super::EncryptFn<N>, super::DecryptFn) {
            match $select {
                $($(#[$attr])* $pat => $crate::rsa_oaep::oaep_pair!(@fns $fns),)*
                // NO-COVERAGE-START
                $($(#[$nattr])* $npat => $crate::rsa_oaep::oaep_pair!(@fns $nfns),)*
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
                    let $f = $crate::cpu::Features(bits);
                    let (encrypt, decrypt) = match $select {
                        $($(#[$attr])* $pat => $crate::rsa_oaep::oaep_pair!(@features $fns),)*
                        // NO-COVERAGE-START
                        $($(#[$nattr])* $npat => panic!("{} chosen for {bits:#b}", stringify!($npat)),)*
                        // NO-COVERAGE-END
                    };
                    assert!($f.contains(encrypt) && $f.contains(decrypt), "{bits:#b}");
                }
            }
        }
    };
    (@fns {
        encrypt: $enc:path [$($ereq:path),*],
        decrypt: $dec:path [$($dreq:path),*] $(,)?
    }) => {
        ($enc, $dec)
    };
    (@features {
        encrypt: $enc:path [$($ereq:path),*],
        decrypt: $dec:path [$($dreq:path),*] $(,)?
    }) => {
        (
            $crate::cpu::Features::all(&[$($ereq),*]),
            $crate::cpu::Features::all(&[$($dreq),*]),
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

#[cfg(target_arch = "aarch64")]
use oaep_pair;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rsa::tests::composite_key;
    use alloc::string::ToString;

    const ALL: [Hash; 12] = [
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

    /// SHA-1 or a SHA-2 function.
    fn sha12(h: Hash) -> bool {
        !matches!(
            h,
            Hash::Md5 | Hash::Sha3_224 | Hash::Sha3_256 | Hash::Sha3_384 | Hash::Sha3_512
        )
    }

    /// On AArch64, the pairs with MGF1 over the same hash function or
    /// SHA-1.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn pairs() {
        let mut n = 0;
        for h in ALL {
            for g in ALL {
                let ok = sha12(h) && (g == h || g == Hash::Sha1);
                assert_eq!(with_functions!(h, g, |_fns| ()).is_some(), ok);
                n += usize::from(ok);
            }
        }
        assert_eq!(n, 13);
    }

    /// On x86-64, every pair of SHA-1 and SHA-2 functions: the zero
    /// ciphertext's encoded message (zero) fails the label's check.
    #[cfg(target_arch = "x86_64")]
    #[test]
    fn pairs() {
        let (private, _) = composite_key();
        for h in ALL {
            for g in ALL {
                let expected = if sha12(h) && sha12(g) {
                    Err(Error::Decryption)
                } else {
                    Err(Error::UnsupportedHash)
                };
                let r = decrypt(&private, &[0; 64], h, g, b"");
                assert_eq!(r, expected, "{h:?} {g:?}");
            }
        }
    }

    #[test]
    fn refused() {
        let (private, public) = composite_key();
        assert_eq!(
            encrypt(&public, b"", Hash::Md5, Hash::Md5, b""),
            Err(Error::UnsupportedHash)
        );
        assert_eq!(
            decrypt(&private, &[0; 64], Hash::Sha256, Hash::Sha3_256, b""),
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

    #[test]
    fn randomness() {
        let mut seed = [0u8; 32];
        os_random(&mut seed).unwrap();
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
