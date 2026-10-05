//! RSAES-OAEP encryption and decryption (RFC 8017 §7.1).
//!
//! [`encrypt`] is the verified `vg_rsa_oaep_<H>_mgf1_<G>_encrypt` (contract
//! `VG.Spec.RsaOaep.encryptContract`), with a seed from the operating
//! system's generator; it encrypts the encoded message with
//! `vg_rsa_public_checked`.
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
//! other pairs are refused ([`Error::UnsupportedHash`]). On a CPU with the
//! SHA extensions or AVX2, and with BMI2 and ADX (and AVX512_IFMA), it uses
//! the faster compression functions and private-key operations, as
//! [`hashes`](crate::hashes) and [`rsa`](crate::rsa) do.
//!
//! This module only checks the lengths, draws the seed and allocates the
//! memory the functions work in.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use crate::cpu::{Features, detected};
use crate::hashes::sha1::Sha1Backend;
use crate::hashes::sha224::Sha224Backend;
use crate::hashes::sha256::Sha256Backend;
use crate::hashes::sha384::Sha384Backend;
use crate::hashes::sha512::Sha512Backend;
use crate::hashes::sha512_224::Sha512_224Backend;
use crate::hashes::sha512_256::Sha512_256Backend;
use crate::rsa::{Backend, PrivateKey, PublicKey, scratch_words};
pub use crate::rsa_pkcs1_sig::Hash;
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

/// The words of working space the functions take
/// (`VG.Spec.RsaPss.scratchWords`).
fn oaep_scratch_words(n_len: usize) -> usize {
    scratch_words(n_len) + 1024
}

/// The operating system's random bytes.
fn os_random(buf: &mut [u8]) -> Result<(), Error> {
    getrandom::fill(buf).map_err(|_| Error::Randomness)
}

/// The type of the implementations of `vg_rsa_oaep_<H>_mgf1_<G>_encrypt`,
/// for `H` of `L` bytes.
type EncryptFn<const L: usize> = unsafe extern "sysv64" fn(
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
) -> u32;

/// An implementation of encryption, by the length of its hash function.
#[derive(Clone, Copy)]
enum Encrypt {
    L20(EncryptFn<20>),
    L28(EncryptFn<28>),
    L32(EncryptFn<32>),
    L48(EncryptFn<48>),
    L64(EncryptFn<64>),
}

/// The type of the implementations of `vg_rsa_oaep_<H>_mgf1_<G>_decrypt`.
type DecryptFn = unsafe extern "sysv64" fn(
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

/// RSAES-OAEP-ENCRYPT (RFC 8017 §7.1.1) with the hash function `hash` and
/// MGF1 over `mgf1_hash`: encrypts `plaintext`, of at most
/// [`modulus_len`](PublicKey::modulus_len)` - 2 hLen - 2` bytes, with `key`
/// and the label `label`, with a random seed, and returns the ciphertext
/// ([`modulus_len`](PublicKey::modulus_len) bytes, big-endian). The timing
/// may depend on the public key and the lengths of the plaintext and the
/// label, not on their contents.
pub fn encrypt(
    key: &PublicKey,
    plaintext: &[u8],
    hash: Hash,
    mgf1_hash: Hash,
    label: &[u8],
) -> Result<Vec<u8>, Error> {
    match encrypt_impl(hash, mgf1_hash, detected()).ok_or(Error::UnsupportedHash)? {
        Encrypt::L20(f) => encrypt_with(key, plaintext, label, f),
        Encrypt::L28(f) => encrypt_with(key, plaintext, label, f),
        Encrypt::L32(f) => encrypt_with(key, plaintext, label, f),
        Encrypt::L48(f) => encrypt_with(key, plaintext, label, f),
        Encrypt::L64(f) => encrypt_with(key, plaintext, label, f),
    }
}

/// The implementation `f` of encryption, with a random seed.
fn encrypt_with<const L: usize>(
    key: &PublicKey,
    plaintext: &[u8],
    label: &[u8],
    f: EncryptFn<L>,
) -> Result<Vec<u8>, Error> {
    let k = key.modulus_len();
    if plaintext.len() + 2 * L + 2 > k {
        return Err(Error::MessageTooLong);
    }
    let mut seed = [0u8; L];
    os_random(&mut seed)?;
    let mut out = vec![0u8; k];
    let mut scratch = vec![0u64; oaep_scratch_words(k)];
    // SAFETY: each pointer is valid for its length (`out` and `scratch` for
    // writes, `seed` for `L` bytes, the hash function's length), and none
    // overlaps another or wraps around, as they are distinct Rust
    // allocations; `PublicKey::new` gives `64 ≤ n_len ≤ 1024`,
    // `1 ≤ e_len ≤ 5 ≤ n_len`, and `out_len = n_len` and
    // `scratch_len = 16 n_len + 1024`; and the CPU has the features of the
    // implementations of the hash functions that `encrypt_impl` chose, which
    // are those of `f`.
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
        )
    };
    // The working space holds the encoded message and its powers.
    zeroize(&mut scratch);
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
    let f = decrypt_impl(hash, mgf1_hash, detected()).ok_or(Error::UnsupportedHash)?;
    let k = key.modulus_len();
    if ciphertext.len() != k {
        return Err(Error::InvalidLength);
    }
    let mut out = vec![0u8; k];
    let mut len = [0u64; 1];
    let mut scratch = vec![0u64; oaep_scratch_words(k)];
    // SAFETY: each pointer is valid for its length (`out`, `len` and
    // `scratch` for writes), and none overlaps another or wraps around, as
    // they are distinct Rust allocations; `PrivateKey::from_crt` and the
    // check above give `64 ≤ n_len ≤ 1024`, `out_len = ct_len = n_len`,
    // `1 ≤ e_len ≤ 5 ≤ n_len`, `1 ≤ p_len < n_len`, `1 ≤ q_len < n_len`,
    // `dp_len = qinv_len = p_len`, `dq_len = q_len` and
    // `scratch_len = 16 n_len + 1024`; and the CPU has the features of the
    // implementations of the hash functions and of the private-key
    // operation that `decrypt_impl` chose, which are those of `f`.
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
    // The working space holds the private key and the encoded message.
    zeroize(&mut scratch);
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

/// `vg_rsa_oaep_sha1_mgf1_sha1_encrypt` for the implementations of Sha1 and
/// Sha1 chosen.
fn encrypt_sha1_mgf1_sha1(h: Sha1Backend) -> EncryptFn<20> {
    use crate::arch::rsa_oaep_sha1_mgf1_sha1::*;
    match h {
        Sha1Backend::Scalar => vg_rsa_oaep_sha1_mgf1_sha1_encrypt,
        Sha1Backend::ShaNi => vg_rsa_oaep_sha1_mgf1_sha1_encrypt_sha1_shani,
    }
}

/// `vg_rsa_oaep_sha1_mgf1_sha1_decrypt` for the implementations of Sha1,
/// Sha1 and the private-key operation chosen.
fn decrypt_sha1_mgf1_sha1(h: Sha1Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha1_mgf1_sha1::*;
    match (h, crt) {
        (Sha1Backend::Scalar, Backend::Baseline) => vg_rsa_oaep_sha1_mgf1_sha1_decrypt,
        (Sha1Backend::Scalar, Backend::Adx) => vg_rsa_oaep_sha1_mgf1_sha1_decrypt_crt_adx,
        (Sha1Backend::Scalar, Backend::Ifma) => vg_rsa_oaep_sha1_mgf1_sha1_decrypt_crt_ifma,
        (Sha1Backend::ShaNi, Backend::Baseline) => vg_rsa_oaep_sha1_mgf1_sha1_decrypt_sha1_shani,
        (Sha1Backend::ShaNi, Backend::Adx) => vg_rsa_oaep_sha1_mgf1_sha1_decrypt_sha1_shani_crt_adx,
        (Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha1_mgf1_sha1_decrypt_sha1_shani_crt_ifma
        }
    }
}

/// `vg_rsa_oaep_sha224_mgf1_sha1_encrypt` for the implementations of Sha224 and
/// Sha1 chosen.
fn encrypt_sha224_mgf1_sha1(h: Sha224Backend, g: Sha1Backend) -> EncryptFn<28> {
    use crate::arch::rsa_oaep_sha224_mgf1_sha1::*;
    match (h, g) {
        (Sha224Backend::Scalar, Sha1Backend::Scalar) => vg_rsa_oaep_sha224_mgf1_sha1_encrypt,
        (Sha224Backend::Scalar, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha224_mgf1_sha1_encrypt_mgf1_shani
        }
        (Sha224Backend::ShaNi, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha224_mgf1_sha1_encrypt_sha224_shani
        }
        (Sha224Backend::ShaNi, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha224_mgf1_sha1_encrypt_sha224_shani_mgf1_shani
        }
        (Sha224Backend::Avx2, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha224_mgf1_sha1_encrypt_sha224_avx2
        }
        (Sha224Backend::Avx2, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha224_mgf1_sha1_encrypt_sha224_avx2_mgf1_shani
        }
    }
}

/// `vg_rsa_oaep_sha224_mgf1_sha1_decrypt` for the implementations of Sha224,
/// Sha1 and the private-key operation chosen.
fn decrypt_sha224_mgf1_sha1(h: Sha224Backend, g: Sha1Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha224_mgf1_sha1::*;
    match (h, g, crt) {
        (Sha224Backend::Scalar, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt
        }
        (Sha224Backend::Scalar, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_crt_adx
        }
        (Sha224Backend::Scalar, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_crt_ifma
        }
        (Sha224Backend::Scalar, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_mgf1_shani
        }
        (Sha224Backend::Scalar, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_mgf1_shani_crt_adx
        }
        (Sha224Backend::Scalar, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_mgf1_shani_crt_ifma
        }
        (Sha224Backend::ShaNi, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_shani
        }
        (Sha224Backend::ShaNi, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_shani_crt_adx
        }
        (Sha224Backend::ShaNi, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_shani_crt_ifma
        }
        (Sha224Backend::ShaNi, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_shani_mgf1_shani
        }
        (Sha224Backend::ShaNi, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_shani_mgf1_shani_crt_adx
        }
        (Sha224Backend::ShaNi, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_shani_mgf1_shani_crt_ifma
        }
        (Sha224Backend::Avx2, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_avx2
        }
        (Sha224Backend::Avx2, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_avx2_crt_adx
        }
        (Sha224Backend::Avx2, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_avx2_crt_ifma
        }
        (Sha224Backend::Avx2, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_avx2_mgf1_shani
        }
        (Sha224Backend::Avx2, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_avx2_mgf1_shani_crt_adx
        }
        (Sha224Backend::Avx2, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_avx2_mgf1_shani_crt_ifma
        }
    }
}

/// `vg_rsa_oaep_sha224_mgf1_sha224_encrypt` for the implementations of Sha224 and
/// Sha224 chosen.
fn encrypt_sha224_mgf1_sha224(h: Sha224Backend) -> EncryptFn<28> {
    use crate::arch::rsa_oaep_sha224_mgf1_sha224::*;
    match h {
        Sha224Backend::Scalar => vg_rsa_oaep_sha224_mgf1_sha224_encrypt,
        Sha224Backend::ShaNi => vg_rsa_oaep_sha224_mgf1_sha224_encrypt_sha224_shani,
        Sha224Backend::Avx2 => vg_rsa_oaep_sha224_mgf1_sha224_encrypt_sha224_avx2,
    }
}

/// `vg_rsa_oaep_sha224_mgf1_sha224_decrypt` for the implementations of Sha224,
/// Sha224 and the private-key operation chosen.
fn decrypt_sha224_mgf1_sha224(h: Sha224Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha224_mgf1_sha224::*;
    match (h, crt) {
        (Sha224Backend::Scalar, Backend::Baseline) => vg_rsa_oaep_sha224_mgf1_sha224_decrypt,
        (Sha224Backend::Scalar, Backend::Adx) => vg_rsa_oaep_sha224_mgf1_sha224_decrypt_crt_adx,
        (Sha224Backend::Scalar, Backend::Ifma) => vg_rsa_oaep_sha224_mgf1_sha224_decrypt_crt_ifma,
        (Sha224Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha224_mgf1_sha224_decrypt_sha224_shani
        }
        (Sha224Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha224_mgf1_sha224_decrypt_sha224_shani_crt_adx
        }
        (Sha224Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha224_mgf1_sha224_decrypt_sha224_shani_crt_ifma
        }
        (Sha224Backend::Avx2, Backend::Baseline) => {
            vg_rsa_oaep_sha224_mgf1_sha224_decrypt_sha224_avx2
        }
        (Sha224Backend::Avx2, Backend::Adx) => {
            vg_rsa_oaep_sha224_mgf1_sha224_decrypt_sha224_avx2_crt_adx
        }
        (Sha224Backend::Avx2, Backend::Ifma) => {
            vg_rsa_oaep_sha224_mgf1_sha224_decrypt_sha224_avx2_crt_ifma
        }
    }
}

/// `vg_rsa_oaep_sha256_mgf1_sha1_encrypt` for the implementations of Sha256 and
/// Sha1 chosen.
fn encrypt_sha256_mgf1_sha1(h: Sha256Backend, g: Sha1Backend) -> EncryptFn<32> {
    use crate::arch::rsa_oaep_sha256_mgf1_sha1::*;
    match (h, g) {
        (Sha256Backend::Scalar, Sha1Backend::Scalar) => vg_rsa_oaep_sha256_mgf1_sha1_encrypt,
        (Sha256Backend::Scalar, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha256_mgf1_sha1_encrypt_mgf1_shani
        }
        (Sha256Backend::ShaNi, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha256_mgf1_sha1_encrypt_sha256_shani
        }
        (Sha256Backend::ShaNi, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha256_mgf1_sha1_encrypt_sha256_shani_mgf1_shani
        }
        (Sha256Backend::Avx2, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha256_mgf1_sha1_encrypt_sha256_avx2
        }
        (Sha256Backend::Avx2, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha256_mgf1_sha1_encrypt_sha256_avx2_mgf1_shani
        }
    }
}

/// `vg_rsa_oaep_sha256_mgf1_sha1_decrypt` for the implementations of Sha256,
/// Sha1 and the private-key operation chosen.
fn decrypt_sha256_mgf1_sha1(h: Sha256Backend, g: Sha1Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha256_mgf1_sha1::*;
    match (h, g, crt) {
        (Sha256Backend::Scalar, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt
        }
        (Sha256Backend::Scalar, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_crt_adx
        }
        (Sha256Backend::Scalar, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_crt_ifma
        }
        (Sha256Backend::Scalar, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_mgf1_shani
        }
        (Sha256Backend::Scalar, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_mgf1_shani_crt_adx
        }
        (Sha256Backend::Scalar, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_mgf1_shani_crt_ifma
        }
        (Sha256Backend::ShaNi, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_shani
        }
        (Sha256Backend::ShaNi, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_shani_crt_adx
        }
        (Sha256Backend::ShaNi, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_shani_crt_ifma
        }
        (Sha256Backend::ShaNi, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_shani_mgf1_shani
        }
        (Sha256Backend::ShaNi, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_shani_mgf1_shani_crt_adx
        }
        (Sha256Backend::ShaNi, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_shani_mgf1_shani_crt_ifma
        }
        (Sha256Backend::Avx2, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_avx2
        }
        (Sha256Backend::Avx2, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_avx2_crt_adx
        }
        (Sha256Backend::Avx2, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_avx2_crt_ifma
        }
        (Sha256Backend::Avx2, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_avx2_mgf1_shani
        }
        (Sha256Backend::Avx2, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_avx2_mgf1_shani_crt_adx
        }
        (Sha256Backend::Avx2, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_avx2_mgf1_shani_crt_ifma
        }
    }
}

/// `vg_rsa_oaep_sha256_mgf1_sha256_encrypt` for the implementations of Sha256 and
/// Sha256 chosen.
fn encrypt_sha256_mgf1_sha256(h: Sha256Backend) -> EncryptFn<32> {
    use crate::arch::rsa_oaep_sha256_mgf1_sha256::*;
    match h {
        Sha256Backend::Scalar => vg_rsa_oaep_sha256_mgf1_sha256_encrypt,
        Sha256Backend::ShaNi => vg_rsa_oaep_sha256_mgf1_sha256_encrypt_sha256_shani,
        Sha256Backend::Avx2 => vg_rsa_oaep_sha256_mgf1_sha256_encrypt_sha256_avx2,
    }
}

/// `vg_rsa_oaep_sha256_mgf1_sha256_decrypt` for the implementations of Sha256,
/// Sha256 and the private-key operation chosen.
fn decrypt_sha256_mgf1_sha256(h: Sha256Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha256_mgf1_sha256::*;
    match (h, crt) {
        (Sha256Backend::Scalar, Backend::Baseline) => vg_rsa_oaep_sha256_mgf1_sha256_decrypt,
        (Sha256Backend::Scalar, Backend::Adx) => vg_rsa_oaep_sha256_mgf1_sha256_decrypt_crt_adx,
        (Sha256Backend::Scalar, Backend::Ifma) => vg_rsa_oaep_sha256_mgf1_sha256_decrypt_crt_ifma,
        (Sha256Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha256_mgf1_sha256_decrypt_sha256_shani
        }
        (Sha256Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha256_mgf1_sha256_decrypt_sha256_shani_crt_adx
        }
        (Sha256Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha256_mgf1_sha256_decrypt_sha256_shani_crt_ifma
        }
        (Sha256Backend::Avx2, Backend::Baseline) => {
            vg_rsa_oaep_sha256_mgf1_sha256_decrypt_sha256_avx2
        }
        (Sha256Backend::Avx2, Backend::Adx) => {
            vg_rsa_oaep_sha256_mgf1_sha256_decrypt_sha256_avx2_crt_adx
        }
        (Sha256Backend::Avx2, Backend::Ifma) => {
            vg_rsa_oaep_sha256_mgf1_sha256_decrypt_sha256_avx2_crt_ifma
        }
    }
}

/// `vg_rsa_oaep_sha384_mgf1_sha1_encrypt` for the implementations of Sha384 and
/// Sha1 chosen.
fn encrypt_sha384_mgf1_sha1(h: Sha384Backend, g: Sha1Backend) -> EncryptFn<48> {
    use crate::arch::rsa_oaep_sha384_mgf1_sha1::*;
    match (h, g) {
        (Sha384Backend::Scalar, Sha1Backend::Scalar) => vg_rsa_oaep_sha384_mgf1_sha1_encrypt,
        (Sha384Backend::Scalar, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha384_mgf1_sha1_encrypt_mgf1_shani
        }
        (Sha384Backend::ShaNi, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha384_mgf1_sha1_encrypt_sha384_shani
        }
        (Sha384Backend::ShaNi, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha384_mgf1_sha1_encrypt_sha384_shani_mgf1_shani
        }
        (Sha384Backend::Avx2, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha384_mgf1_sha1_encrypt_sha384_avx2
        }
        (Sha384Backend::Avx2, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha384_mgf1_sha1_encrypt_sha384_avx2_mgf1_shani
        }
    }
}

/// `vg_rsa_oaep_sha384_mgf1_sha1_decrypt` for the implementations of Sha384,
/// Sha1 and the private-key operation chosen.
fn decrypt_sha384_mgf1_sha1(h: Sha384Backend, g: Sha1Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha384_mgf1_sha1::*;
    match (h, g, crt) {
        (Sha384Backend::Scalar, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt
        }
        (Sha384Backend::Scalar, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_crt_adx
        }
        (Sha384Backend::Scalar, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_crt_ifma
        }
        (Sha384Backend::Scalar, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_mgf1_shani
        }
        (Sha384Backend::Scalar, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_mgf1_shani_crt_adx
        }
        (Sha384Backend::Scalar, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_mgf1_shani_crt_ifma
        }
        (Sha384Backend::ShaNi, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_shani
        }
        (Sha384Backend::ShaNi, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_shani_crt_adx
        }
        (Sha384Backend::ShaNi, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_shani_crt_ifma
        }
        (Sha384Backend::ShaNi, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_shani_mgf1_shani
        }
        (Sha384Backend::ShaNi, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_shani_mgf1_shani_crt_adx
        }
        (Sha384Backend::ShaNi, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_shani_mgf1_shani_crt_ifma
        }
        (Sha384Backend::Avx2, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_avx2
        }
        (Sha384Backend::Avx2, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_avx2_crt_adx
        }
        (Sha384Backend::Avx2, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_avx2_crt_ifma
        }
        (Sha384Backend::Avx2, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_avx2_mgf1_shani
        }
        (Sha384Backend::Avx2, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_avx2_mgf1_shani_crt_adx
        }
        (Sha384Backend::Avx2, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_avx2_mgf1_shani_crt_ifma
        }
    }
}

/// `vg_rsa_oaep_sha384_mgf1_sha384_encrypt` for the implementations of Sha384 and
/// Sha384 chosen.
fn encrypt_sha384_mgf1_sha384(h: Sha384Backend) -> EncryptFn<48> {
    use crate::arch::rsa_oaep_sha384_mgf1_sha384::*;
    match h {
        Sha384Backend::Scalar => vg_rsa_oaep_sha384_mgf1_sha384_encrypt,
        Sha384Backend::ShaNi => vg_rsa_oaep_sha384_mgf1_sha384_encrypt_sha384_shani,
        Sha384Backend::Avx2 => vg_rsa_oaep_sha384_mgf1_sha384_encrypt_sha384_avx2,
    }
}

/// `vg_rsa_oaep_sha384_mgf1_sha384_decrypt` for the implementations of Sha384,
/// Sha384 and the private-key operation chosen.
fn decrypt_sha384_mgf1_sha384(h: Sha384Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha384_mgf1_sha384::*;
    match (h, crt) {
        (Sha384Backend::Scalar, Backend::Baseline) => vg_rsa_oaep_sha384_mgf1_sha384_decrypt,
        (Sha384Backend::Scalar, Backend::Adx) => vg_rsa_oaep_sha384_mgf1_sha384_decrypt_crt_adx,
        (Sha384Backend::Scalar, Backend::Ifma) => vg_rsa_oaep_sha384_mgf1_sha384_decrypt_crt_ifma,
        (Sha384Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha384_mgf1_sha384_decrypt_sha384_shani
        }
        (Sha384Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha384_mgf1_sha384_decrypt_sha384_shani_crt_adx
        }
        (Sha384Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha384_mgf1_sha384_decrypt_sha384_shani_crt_ifma
        }
        (Sha384Backend::Avx2, Backend::Baseline) => {
            vg_rsa_oaep_sha384_mgf1_sha384_decrypt_sha384_avx2
        }
        (Sha384Backend::Avx2, Backend::Adx) => {
            vg_rsa_oaep_sha384_mgf1_sha384_decrypt_sha384_avx2_crt_adx
        }
        (Sha384Backend::Avx2, Backend::Ifma) => {
            vg_rsa_oaep_sha384_mgf1_sha384_decrypt_sha384_avx2_crt_ifma
        }
    }
}

/// `vg_rsa_oaep_sha512_mgf1_sha1_encrypt` for the implementations of Sha512 and
/// Sha1 chosen.
fn encrypt_sha512_mgf1_sha1(h: Sha512Backend, g: Sha1Backend) -> EncryptFn<64> {
    use crate::arch::rsa_oaep_sha512_mgf1_sha1::*;
    match (h, g) {
        (Sha512Backend::Scalar, Sha1Backend::Scalar) => vg_rsa_oaep_sha512_mgf1_sha1_encrypt,
        (Sha512Backend::Scalar, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha512_mgf1_sha1_encrypt_mgf1_shani
        }
        (Sha512Backend::ShaNi, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha512_mgf1_sha1_encrypt_sha512_shani
        }
        (Sha512Backend::ShaNi, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha512_mgf1_sha1_encrypt_sha512_shani_mgf1_shani
        }
        (Sha512Backend::Avx2, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha512_mgf1_sha1_encrypt_sha512_avx2
        }
        (Sha512Backend::Avx2, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha512_mgf1_sha1_encrypt_sha512_avx2_mgf1_shani
        }
    }
}

/// `vg_rsa_oaep_sha512_mgf1_sha1_decrypt` for the implementations of Sha512,
/// Sha1 and the private-key operation chosen.
fn decrypt_sha512_mgf1_sha1(h: Sha512Backend, g: Sha1Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha512_mgf1_sha1::*;
    match (h, g, crt) {
        (Sha512Backend::Scalar, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt
        }
        (Sha512Backend::Scalar, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_crt_adx
        }
        (Sha512Backend::Scalar, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_crt_ifma
        }
        (Sha512Backend::Scalar, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_mgf1_shani
        }
        (Sha512Backend::Scalar, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_mgf1_shani_crt_adx
        }
        (Sha512Backend::Scalar, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_mgf1_shani_crt_ifma
        }
        (Sha512Backend::ShaNi, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_shani
        }
        (Sha512Backend::ShaNi, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_shani_crt_adx
        }
        (Sha512Backend::ShaNi, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_shani_crt_ifma
        }
        (Sha512Backend::ShaNi, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_shani_mgf1_shani
        }
        (Sha512Backend::ShaNi, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_shani_mgf1_shani_crt_adx
        }
        (Sha512Backend::ShaNi, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_shani_mgf1_shani_crt_ifma
        }
        (Sha512Backend::Avx2, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_avx2
        }
        (Sha512Backend::Avx2, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_avx2_crt_adx
        }
        (Sha512Backend::Avx2, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_avx2_crt_ifma
        }
        (Sha512Backend::Avx2, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_avx2_mgf1_shani
        }
        (Sha512Backend::Avx2, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_avx2_mgf1_shani_crt_adx
        }
        (Sha512Backend::Avx2, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_avx2_mgf1_shani_crt_ifma
        }
    }
}

/// `vg_rsa_oaep_sha512_mgf1_sha512_encrypt` for the implementations of Sha512 and
/// Sha512 chosen.
fn encrypt_sha512_mgf1_sha512(h: Sha512Backend) -> EncryptFn<64> {
    use crate::arch::rsa_oaep_sha512_mgf1_sha512::*;
    match h {
        Sha512Backend::Scalar => vg_rsa_oaep_sha512_mgf1_sha512_encrypt,
        Sha512Backend::ShaNi => vg_rsa_oaep_sha512_mgf1_sha512_encrypt_sha512_shani,
        Sha512Backend::Avx2 => vg_rsa_oaep_sha512_mgf1_sha512_encrypt_sha512_avx2,
    }
}

/// `vg_rsa_oaep_sha512_mgf1_sha512_decrypt` for the implementations of Sha512,
/// Sha512 and the private-key operation chosen.
fn decrypt_sha512_mgf1_sha512(h: Sha512Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha512_mgf1_sha512::*;
    match (h, crt) {
        (Sha512Backend::Scalar, Backend::Baseline) => vg_rsa_oaep_sha512_mgf1_sha512_decrypt,
        (Sha512Backend::Scalar, Backend::Adx) => vg_rsa_oaep_sha512_mgf1_sha512_decrypt_crt_adx,
        (Sha512Backend::Scalar, Backend::Ifma) => vg_rsa_oaep_sha512_mgf1_sha512_decrypt_crt_ifma,
        (Sha512Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha512_mgf1_sha512_decrypt_sha512_shani
        }
        (Sha512Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha512_mgf1_sha512_decrypt_sha512_shani_crt_adx
        }
        (Sha512Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha512_mgf1_sha512_decrypt_sha512_shani_crt_ifma
        }
        (Sha512Backend::Avx2, Backend::Baseline) => {
            vg_rsa_oaep_sha512_mgf1_sha512_decrypt_sha512_avx2
        }
        (Sha512Backend::Avx2, Backend::Adx) => {
            vg_rsa_oaep_sha512_mgf1_sha512_decrypt_sha512_avx2_crt_adx
        }
        (Sha512Backend::Avx2, Backend::Ifma) => {
            vg_rsa_oaep_sha512_mgf1_sha512_decrypt_sha512_avx2_crt_ifma
        }
    }
}

/// `vg_rsa_oaep_sha512_224_mgf1_sha1_encrypt` for the implementations of Sha512_224 and
/// Sha1 chosen.
fn encrypt_sha512_224_mgf1_sha1(h: Sha512_224Backend, g: Sha1Backend) -> EncryptFn<28> {
    use crate::arch::rsa_oaep_sha512_224_mgf1_sha1::*;
    match (h, g) {
        (Sha512_224Backend::Scalar, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_encrypt
        }
        (Sha512_224Backend::Scalar, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_encrypt_mgf1_shani
        }
        (Sha512_224Backend::ShaNi, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_encrypt_sha512_224_shani
        }
        (Sha512_224Backend::ShaNi, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_encrypt_sha512_224_shani_mgf1_shani
        }
        (Sha512_224Backend::Avx2, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_encrypt_sha512_224_avx2
        }
        (Sha512_224Backend::Avx2, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_encrypt_sha512_224_avx2_mgf1_shani
        }
    }
}

/// `vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt` for the implementations of Sha512_224,
/// Sha1 and the private-key operation chosen.
fn decrypt_sha512_224_mgf1_sha1(h: Sha512_224Backend, g: Sha1Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha512_224_mgf1_sha1::*;
    match (h, g, crt) {
        (Sha512_224Backend::Scalar, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt
        }
        (Sha512_224Backend::Scalar, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_crt_adx
        }
        (Sha512_224Backend::Scalar, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_crt_ifma
        }
        (Sha512_224Backend::Scalar, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_mgf1_shani
        }
        (Sha512_224Backend::Scalar, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_mgf1_shani_crt_adx
        }
        (Sha512_224Backend::Scalar, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_mgf1_shani_crt_ifma
        }
        (Sha512_224Backend::ShaNi, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_shani
        }
        (Sha512_224Backend::ShaNi, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_shani_crt_adx
        }
        (Sha512_224Backend::ShaNi, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_shani_crt_ifma
        }
        (Sha512_224Backend::ShaNi, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_shani_mgf1_shani
        }
        (Sha512_224Backend::ShaNi, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_shani_mgf1_shani_crt_adx
        }
        (Sha512_224Backend::ShaNi, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_shani_mgf1_shani_crt_ifma
        }
        (Sha512_224Backend::Avx2, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_avx2
        }
        (Sha512_224Backend::Avx2, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_avx2_crt_adx
        }
        (Sha512_224Backend::Avx2, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_avx2_crt_ifma
        }
        (Sha512_224Backend::Avx2, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_avx2_mgf1_shani
        }
        (Sha512_224Backend::Avx2, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_avx2_mgf1_shani_crt_adx
        }
        (Sha512_224Backend::Avx2, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_avx2_mgf1_shani_crt_ifma
        }
    }
}

/// `vg_rsa_oaep_sha512_224_mgf1_sha512_224_encrypt` for the implementations of Sha512_224 and
/// Sha512_224 chosen.
fn encrypt_sha512_224_mgf1_sha512_224(h: Sha512_224Backend) -> EncryptFn<28> {
    use crate::arch::rsa_oaep_sha512_224_mgf1_sha512_224::*;
    match h {
        Sha512_224Backend::Scalar => vg_rsa_oaep_sha512_224_mgf1_sha512_224_encrypt,
        Sha512_224Backend::ShaNi => vg_rsa_oaep_sha512_224_mgf1_sha512_224_encrypt_sha512_224_shani,
        Sha512_224Backend::Avx2 => vg_rsa_oaep_sha512_224_mgf1_sha512_224_encrypt_sha512_224_avx2,
    }
}

/// `vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt` for the implementations of Sha512_224,
/// Sha512_224 and the private-key operation chosen.
fn decrypt_sha512_224_mgf1_sha512_224(h: Sha512_224Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha512_224_mgf1_sha512_224::*;
    match (h, crt) {
        (Sha512_224Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt
        }
        (Sha512_224Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt_crt_adx
        }
        (Sha512_224Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt_crt_ifma
        }
        (Sha512_224Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt_sha512_224_shani
        }
        (Sha512_224Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt_sha512_224_shani_crt_adx
        }
        (Sha512_224Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt_sha512_224_shani_crt_ifma
        }
        (Sha512_224Backend::Avx2, Backend::Baseline) => {
            vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt_sha512_224_avx2
        }
        (Sha512_224Backend::Avx2, Backend::Adx) => {
            vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt_sha512_224_avx2_crt_adx
        }
        (Sha512_224Backend::Avx2, Backend::Ifma) => {
            vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt_sha512_224_avx2_crt_ifma
        }
    }
}

/// `vg_rsa_oaep_sha512_256_mgf1_sha1_encrypt` for the implementations of Sha512_256 and
/// Sha1 chosen.
fn encrypt_sha512_256_mgf1_sha1(h: Sha512_256Backend, g: Sha1Backend) -> EncryptFn<32> {
    use crate::arch::rsa_oaep_sha512_256_mgf1_sha1::*;
    match (h, g) {
        (Sha512_256Backend::Scalar, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_encrypt
        }
        (Sha512_256Backend::Scalar, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_encrypt_mgf1_shani
        }
        (Sha512_256Backend::ShaNi, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_encrypt_sha512_256_shani
        }
        (Sha512_256Backend::ShaNi, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_encrypt_sha512_256_shani_mgf1_shani
        }
        (Sha512_256Backend::Avx2, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_encrypt_sha512_256_avx2
        }
        (Sha512_256Backend::Avx2, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_encrypt_sha512_256_avx2_mgf1_shani
        }
    }
}

/// `vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt` for the implementations of Sha512_256,
/// Sha1 and the private-key operation chosen.
fn decrypt_sha512_256_mgf1_sha1(h: Sha512_256Backend, g: Sha1Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha512_256_mgf1_sha1::*;
    match (h, g, crt) {
        (Sha512_256Backend::Scalar, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt
        }
        (Sha512_256Backend::Scalar, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_crt_adx
        }
        (Sha512_256Backend::Scalar, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_crt_ifma
        }
        (Sha512_256Backend::Scalar, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_mgf1_shani
        }
        (Sha512_256Backend::Scalar, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_mgf1_shani_crt_adx
        }
        (Sha512_256Backend::Scalar, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_mgf1_shani_crt_ifma
        }
        (Sha512_256Backend::ShaNi, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_shani
        }
        (Sha512_256Backend::ShaNi, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_shani_crt_adx
        }
        (Sha512_256Backend::ShaNi, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_shani_crt_ifma
        }
        (Sha512_256Backend::ShaNi, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_shani_mgf1_shani
        }
        (Sha512_256Backend::ShaNi, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_shani_mgf1_shani_crt_adx
        }
        (Sha512_256Backend::ShaNi, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_shani_mgf1_shani_crt_ifma
        }
        (Sha512_256Backend::Avx2, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_avx2
        }
        (Sha512_256Backend::Avx2, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_avx2_crt_adx
        }
        (Sha512_256Backend::Avx2, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_avx2_crt_ifma
        }
        (Sha512_256Backend::Avx2, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_avx2_mgf1_shani
        }
        (Sha512_256Backend::Avx2, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_avx2_mgf1_shani_crt_adx
        }
        (Sha512_256Backend::Avx2, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_avx2_mgf1_shani_crt_ifma
        }
    }
}

/// `vg_rsa_oaep_sha512_256_mgf1_sha512_256_encrypt` for the implementations of Sha512_256 and
/// Sha512_256 chosen.
fn encrypt_sha512_256_mgf1_sha512_256(h: Sha512_256Backend) -> EncryptFn<32> {
    use crate::arch::rsa_oaep_sha512_256_mgf1_sha512_256::*;
    match h {
        Sha512_256Backend::Scalar => vg_rsa_oaep_sha512_256_mgf1_sha512_256_encrypt,
        Sha512_256Backend::ShaNi => vg_rsa_oaep_sha512_256_mgf1_sha512_256_encrypt_sha512_256_shani,
        Sha512_256Backend::Avx2 => vg_rsa_oaep_sha512_256_mgf1_sha512_256_encrypt_sha512_256_avx2,
    }
}

/// `vg_rsa_oaep_sha512_256_mgf1_sha512_256_decrypt` for the implementations of Sha512_256,
/// Sha512_256 and the private-key operation chosen.
fn decrypt_sha512_256_mgf1_sha512_256(h: Sha512_256Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha512_256_mgf1_sha512_256::*;
    match (h, crt) {
        (Sha512_256Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_256_mgf1_sha512_256_decrypt
        }
        (Sha512_256Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha512_256_mgf1_sha512_256_decrypt_crt_adx
        }
        (Sha512_256Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha512_256_mgf1_sha512_256_decrypt_crt_ifma
        }
        (Sha512_256Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha512_256_mgf1_sha512_256_decrypt_sha512_256_shani
        }
        (Sha512_256Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha512_256_mgf1_sha512_256_decrypt_sha512_256_shani_crt_adx
        }
        (Sha512_256Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha512_256_mgf1_sha512_256_decrypt_sha512_256_shani_crt_ifma
        }
        (Sha512_256Backend::Avx2, Backend::Baseline) => {
            vg_rsa_oaep_sha512_256_mgf1_sha512_256_decrypt_sha512_256_avx2
        }
        (Sha512_256Backend::Avx2, Backend::Adx) => {
            vg_rsa_oaep_sha512_256_mgf1_sha512_256_decrypt_sha512_256_avx2_crt_adx
        }
        (Sha512_256Backend::Avx2, Backend::Ifma) => {
            vg_rsa_oaep_sha512_256_mgf1_sha512_256_decrypt_sha512_256_avx2_crt_ifma
        }
    }
}

/// The implementation of encryption for `hash` and `mgf1_hash`, if they
/// are a pair this module supports, for a CPU with the features `f`.
fn encrypt_impl(hash: Hash, mgf1_hash: Hash, f: Features) -> Option<Encrypt> {
    Some(match (hash, mgf1_hash) {
        (Hash::Sha1, Hash::Sha1) => Encrypt::L20(encrypt_sha1_mgf1_sha1(Sha1Backend::select(f))),
        (Hash::Sha224, Hash::Sha1) => Encrypt::L28(encrypt_sha224_mgf1_sha1(
            Sha224Backend::select(f),
            Sha1Backend::select(f),
        )),
        (Hash::Sha224, Hash::Sha224) => {
            Encrypt::L28(encrypt_sha224_mgf1_sha224(Sha224Backend::select(f)))
        }
        (Hash::Sha256, Hash::Sha1) => Encrypt::L32(encrypt_sha256_mgf1_sha1(
            Sha256Backend::select(f),
            Sha1Backend::select(f),
        )),
        (Hash::Sha256, Hash::Sha256) => {
            Encrypt::L32(encrypt_sha256_mgf1_sha256(Sha256Backend::select(f)))
        }
        (Hash::Sha384, Hash::Sha1) => Encrypt::L48(encrypt_sha384_mgf1_sha1(
            Sha384Backend::select(f),
            Sha1Backend::select(f),
        )),
        (Hash::Sha384, Hash::Sha384) => {
            Encrypt::L48(encrypt_sha384_mgf1_sha384(Sha384Backend::select(f)))
        }
        (Hash::Sha512, Hash::Sha1) => Encrypt::L64(encrypt_sha512_mgf1_sha1(
            Sha512Backend::select(f),
            Sha1Backend::select(f),
        )),
        (Hash::Sha512, Hash::Sha512) => {
            Encrypt::L64(encrypt_sha512_mgf1_sha512(Sha512Backend::select(f)))
        }
        (Hash::Sha512_224, Hash::Sha1) => Encrypt::L28(encrypt_sha512_224_mgf1_sha1(
            Sha512_224Backend::select(f),
            Sha1Backend::select(f),
        )),
        (Hash::Sha512_224, Hash::Sha512_224) => Encrypt::L28(encrypt_sha512_224_mgf1_sha512_224(
            Sha512_224Backend::select(f),
        )),
        (Hash::Sha512_256, Hash::Sha1) => Encrypt::L32(encrypt_sha512_256_mgf1_sha1(
            Sha512_256Backend::select(f),
            Sha1Backend::select(f),
        )),
        (Hash::Sha512_256, Hash::Sha512_256) => Encrypt::L32(encrypt_sha512_256_mgf1_sha512_256(
            Sha512_256Backend::select(f),
        )),
        _ => return None,
    })
}

/// The implementation of decryption for `hash` and `mgf1_hash`, if they
/// are a pair this module supports, for a CPU with the features `f`.
fn decrypt_impl(hash: Hash, mgf1_hash: Hash, f: Features) -> Option<DecryptFn> {
    let crt = Backend::select(f);
    Some(match (hash, mgf1_hash) {
        (Hash::Sha1, Hash::Sha1) => decrypt_sha1_mgf1_sha1(Sha1Backend::select(f), crt),
        (Hash::Sha224, Hash::Sha1) => {
            decrypt_sha224_mgf1_sha1(Sha224Backend::select(f), Sha1Backend::select(f), crt)
        }
        (Hash::Sha224, Hash::Sha224) => decrypt_sha224_mgf1_sha224(Sha224Backend::select(f), crt),
        (Hash::Sha256, Hash::Sha1) => {
            decrypt_sha256_mgf1_sha1(Sha256Backend::select(f), Sha1Backend::select(f), crt)
        }
        (Hash::Sha256, Hash::Sha256) => decrypt_sha256_mgf1_sha256(Sha256Backend::select(f), crt),
        (Hash::Sha384, Hash::Sha1) => {
            decrypt_sha384_mgf1_sha1(Sha384Backend::select(f), Sha1Backend::select(f), crt)
        }
        (Hash::Sha384, Hash::Sha384) => decrypt_sha384_mgf1_sha384(Sha384Backend::select(f), crt),
        (Hash::Sha512, Hash::Sha1) => {
            decrypt_sha512_mgf1_sha1(Sha512Backend::select(f), Sha1Backend::select(f), crt)
        }
        (Hash::Sha512, Hash::Sha512) => decrypt_sha512_mgf1_sha512(Sha512Backend::select(f), crt),
        (Hash::Sha512_224, Hash::Sha1) => {
            decrypt_sha512_224_mgf1_sha1(Sha512_224Backend::select(f), Sha1Backend::select(f), crt)
        }
        (Hash::Sha512_224, Hash::Sha512_224) => {
            decrypt_sha512_224_mgf1_sha512_224(Sha512_224Backend::select(f), crt)
        }
        (Hash::Sha512_256, Hash::Sha1) => {
            decrypt_sha512_256_mgf1_sha1(Sha512_256Backend::select(f), Sha1Backend::select(f), crt)
        }
        (Hash::Sha512_256, Hash::Sha512_256) => {
            decrypt_sha512_256_mgf1_sha512_256(Sha512_256Backend::select(f), crt)
        }
        _ => return None,
    })
}

/// Every implementation of every pair, each once.
#[cfg(test)]
fn all_impls() -> (Vec<Encrypt>, Vec<DecryptFn>) {
    let (mut e, mut d) = (Vec::new(), Vec::new());
    for h in [Sha1Backend::Scalar, Sha1Backend::ShaNi] {
        e.push(Encrypt::L20(encrypt_sha1_mgf1_sha1(h)));
        for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
            d.push(decrypt_sha1_mgf1_sha1(h, crt));
        }
    }
    for h in [
        Sha224Backend::Scalar,
        Sha224Backend::ShaNi,
        Sha224Backend::Avx2,
    ] {
        for g in [Sha1Backend::Scalar, Sha1Backend::ShaNi] {
            e.push(Encrypt::L28(encrypt_sha224_mgf1_sha1(h, g)));
            for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
                d.push(decrypt_sha224_mgf1_sha1(h, g, crt));
            }
        }
    }
    for h in [
        Sha224Backend::Scalar,
        Sha224Backend::ShaNi,
        Sha224Backend::Avx2,
    ] {
        e.push(Encrypt::L28(encrypt_sha224_mgf1_sha224(h)));
        for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
            d.push(decrypt_sha224_mgf1_sha224(h, crt));
        }
    }
    for h in [
        Sha256Backend::Scalar,
        Sha256Backend::ShaNi,
        Sha256Backend::Avx2,
    ] {
        for g in [Sha1Backend::Scalar, Sha1Backend::ShaNi] {
            e.push(Encrypt::L32(encrypt_sha256_mgf1_sha1(h, g)));
            for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
                d.push(decrypt_sha256_mgf1_sha1(h, g, crt));
            }
        }
    }
    for h in [
        Sha256Backend::Scalar,
        Sha256Backend::ShaNi,
        Sha256Backend::Avx2,
    ] {
        e.push(Encrypt::L32(encrypt_sha256_mgf1_sha256(h)));
        for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
            d.push(decrypt_sha256_mgf1_sha256(h, crt));
        }
    }
    for h in [
        Sha384Backend::Scalar,
        Sha384Backend::ShaNi,
        Sha384Backend::Avx2,
    ] {
        for g in [Sha1Backend::Scalar, Sha1Backend::ShaNi] {
            e.push(Encrypt::L48(encrypt_sha384_mgf1_sha1(h, g)));
            for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
                d.push(decrypt_sha384_mgf1_sha1(h, g, crt));
            }
        }
    }
    for h in [
        Sha384Backend::Scalar,
        Sha384Backend::ShaNi,
        Sha384Backend::Avx2,
    ] {
        e.push(Encrypt::L48(encrypt_sha384_mgf1_sha384(h)));
        for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
            d.push(decrypt_sha384_mgf1_sha384(h, crt));
        }
    }
    for h in [
        Sha512Backend::Scalar,
        Sha512Backend::ShaNi,
        Sha512Backend::Avx2,
    ] {
        for g in [Sha1Backend::Scalar, Sha1Backend::ShaNi] {
            e.push(Encrypt::L64(encrypt_sha512_mgf1_sha1(h, g)));
            for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
                d.push(decrypt_sha512_mgf1_sha1(h, g, crt));
            }
        }
    }
    for h in [
        Sha512Backend::Scalar,
        Sha512Backend::ShaNi,
        Sha512Backend::Avx2,
    ] {
        e.push(Encrypt::L64(encrypt_sha512_mgf1_sha512(h)));
        for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
            d.push(decrypt_sha512_mgf1_sha512(h, crt));
        }
    }
    for h in [
        Sha512_224Backend::Scalar,
        Sha512_224Backend::ShaNi,
        Sha512_224Backend::Avx2,
    ] {
        for g in [Sha1Backend::Scalar, Sha1Backend::ShaNi] {
            e.push(Encrypt::L28(encrypt_sha512_224_mgf1_sha1(h, g)));
            for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
                d.push(decrypt_sha512_224_mgf1_sha1(h, g, crt));
            }
        }
    }
    for h in [
        Sha512_224Backend::Scalar,
        Sha512_224Backend::ShaNi,
        Sha512_224Backend::Avx2,
    ] {
        e.push(Encrypt::L28(encrypt_sha512_224_mgf1_sha512_224(h)));
        for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
            d.push(decrypt_sha512_224_mgf1_sha512_224(h, crt));
        }
    }
    for h in [
        Sha512_256Backend::Scalar,
        Sha512_256Backend::ShaNi,
        Sha512_256Backend::Avx2,
    ] {
        for g in [Sha1Backend::Scalar, Sha1Backend::ShaNi] {
            e.push(Encrypt::L32(encrypt_sha512_256_mgf1_sha1(h, g)));
            for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
                d.push(decrypt_sha512_256_mgf1_sha1(h, g, crt));
            }
        }
    }
    for h in [
        Sha512_256Backend::Scalar,
        Sha512_256Backend::ShaNi,
        Sha512_256Backend::Avx2,
    ] {
        e.push(Encrypt::L32(encrypt_sha512_256_mgf1_sha512_256(h)));
        for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
            d.push(decrypt_sha512_256_mgf1_sha512_256(h, crt));
        }
    }
    (e, d)
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::ToString;

    /// Every implementation of every pair is distinct (each is tested end
    /// to end on a CPU that chooses it).
    #[test]
    fn rsa_oaep_backends() {
        let (e, d) = all_impls();
        let mut fns: Vec<usize> = e
            .iter()
            .map(|e| match *e {
                Encrypt::L20(f) => f as usize,
                Encrypt::L28(f) => f as usize,
                Encrypt::L32(f) => f as usize,
                Encrypt::L48(f) => f as usize,
                Encrypt::L64(f) => f as usize,
            })
            .chain(d.iter().map(|&f| f as usize))
            .collect();
        fns.sort_unstable();
        fns.dedup();
        assert_eq!(fns.len(), 56 + 168);
    }

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
                assert_eq!(encrypt_impl(h, g, detected()).is_some(), ok);
                assert_eq!(decrypt_impl(h, g, detected()).is_some(), ok);
                n += usize::from(ok);
            }
        }
        assert_eq!(n, 13);
    }

    /// The product of the big-endian numbers `a` and `b`, big-endian.
    fn mul(a: &[u8], b: &[u8]) -> Vec<u8> {
        let mut r = vec![0u32; a.len() + b.len()];
        for (i, &x) in a.iter().rev().enumerate() {
            for (j, &y) in b.iter().rev().enumerate() {
                r[i + j] += u32::from(x) * u32::from(y);
            }
            for t in i..r.len() - 1 {
                r[t + 1] += r[t] >> 8;
                r[t] &= 0xff;
            }
        }
        r.iter().rev().map(|&x| x as u8).collect()
    }

    /// A 64-byte key `p q = n` of two odd numbers with `e = 3`,
    /// `dP = dQ = 1` and `qInv = 0`, which `PrivateKey::from_crt` accepts
    /// but whose private-key operation fails the check for 2.
    fn key() -> (PrivateKey, PublicKey) {
        let p = vec![0xff; 32];
        let mut q = vec![0xff; 32];
        q[31] = 0xfd;
        let n = mul(&p, &q);
        let private = PrivateKey::from_crt(&n, &[3], &[1], &p, &q, &[1], &[1], &[0]).unwrap();
        (private, PublicKey::new(&n, &[3]).unwrap())
    }

    #[test]
    fn refused() {
        let (private, public) = key();
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
