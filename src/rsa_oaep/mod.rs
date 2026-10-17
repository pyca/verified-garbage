//! RSAES-OAEP encryption and decryption (RFC 8017 §7.1).
//!
//! [`encrypt`] is the verified `vg_rsa_oaep_encrypt_precomputed` (contract
//! `VG.Spec.RsaOaep.encryptAnyContract`), which takes the hash functions as
//! arguments, by their numbers (`VG.Spec.HashId`). It runs with a seed from
//! the operating system's generator; it encrypts the encoded message with
//! `vg_rsa_public_precomputed_checked`, reusing the public key's precomputed
//! modulus values (on x86-64, with ADX multiplication when available).
//!
//! [`decrypt`] is the verified `vg_rsa_oaep_decrypt` (contract
//! `VG.Spec.RsaOaep.decryptAnyContract`), which computes the encoded message
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
//! `any.rs` names the verified functions for each choice of those
//! implementations (a tier of the hash functions', `Tier`).
//!
//! This module only checks the lengths, draws the seed and allocates the
//! memory the functions work in.

#![cfg(all(
    any(target_arch = "x86_64", target_arch = "aarch64"),
    feature = "alloc"
))]

mod any;

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
/// and C's on AArch64.
macro_rules! verified_fn_types {
    ($(
        $(#[$doc:meta])*
        type $name:ident $(<const $l:ident: usize>)? = fn($($arg:ty),* $(,)?) -> $ret:ty;
    )*) => {$(
        $(#[$doc])*
        #[cfg(target_arch = "x86_64")]
        type $name $(<const $l: usize>)? = unsafe extern "sysv64" fn($($arg),*) -> $ret;
        $(#[$doc])*
        #[cfg(target_arch = "aarch64")]
        type $name $(<const $l: usize>)? = unsafe extern "C" fn($($arg),*) -> $ret;
    )*};
}

verified_fn_types! {
    /// The type of the implementations of `vg_rsa_oaep_encrypt_precomputed`.
    type EncryptAnyFn = fn(
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
        *const u8,
        usize,
        *mut u64,
        usize,
        *const u64,
        usize,
        usize,
        usize,
    ) -> u32;

    /// The type of the implementations of `vg_rsa_oaep_decrypt`.
    type DecryptAnyFn = fn(
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
        usize,
        usize,
    ) -> u32;

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
    if !supported(hash, mgf1_hash) {
        return Err(Error::UnsupportedHash);
    }
    encrypt_with(
        key,
        plaintext,
        hash,
        mgf1_hash,
        label,
        any::functions(detected()).0,
    )
}

/// Whether this module supports the hash function `hash` with MGF1 over
/// `mgf1_hash`: SHA-1 or SHA-2, with MGF1 over itself or SHA-1.
fn supported(hash: Hash, mgf1_hash: Hash) -> bool {
    matches!(
        hash,
        Hash::Sha1
            | Hash::Sha224
            | Hash::Sha256
            | Hash::Sha384
            | Hash::Sha512
            | Hash::Sha512_224
            | Hash::Sha512_256
    ) && (mgf1_hash == hash || mgf1_hash == Hash::Sha1)
}

/// `f`, a `vg_rsa_oaep_encrypt_precomputed` that this CPU can run, with the
/// hash functions `hash` and `mgf1_hash`, which `supported` accepts, and a
/// random seed.
fn encrypt_with(
    key: &PublicKey,
    plaintext: &[u8],
    hash: Hash,
    mgf1_hash: Hash,
    label: &[u8],
    f: EncryptAnyFn,
) -> Result<Vec<u8>, Error> {
    let k = key.modulus_len();
    let l = hash.digest_len();
    if plaintext.len() + 2 * l + 2 > k {
        return Err(Error::MessageTooLong);
    }
    let mut buf = [0u8; 64];
    let seed = &mut buf[..l];
    os_random(seed)?;
    let mut out = vec![0u8; k];
    let mut scratch = key.verify_scratch.take(public_scratch_words(k), true);
    let pre = key.pre(&mut scratch);
    // SAFETY: each pointer is valid for its length (`out` and `scratch` for
    // writes), and none overlaps another or wraps around, as they are
    // distinct Rust allocations; `hash` and `mgf1_hash` are SHA-1 or SHA-2,
    // whose numbers are in 1..=7, and `seed_len` is `hash`'s length;
    // `PublicKey::new` gives `64 ≤ n_len ≤ 1024`, `1 ≤ e_len ≤ 5 ≤ n_len`,
    // and `out_len = n_len` and `scratch_len = 8 ⌈n_len / 8⌉ + 1072`; `pre`
    // holds the verified precomputation for `key.n`, with
    // `2 * ceil(n_len / 8)` words; and the CPU has the features of `f`,
    // which `any::functions` chose for the features detected (its
    // `backend_features` test checks that they need no others).
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
            seed.as_ptr(),
            l,
            scratch.as_mut_ptr(),
            scratch.len(),
            pre.as_ptr(),
            pre.len(),
            hash as usize,
            mgf1_hash as usize,
        )
    };
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
    if !supported(hash, mgf1_hash) {
        return Err(Error::UnsupportedHash);
    }
    decrypt_with(
        key,
        ciphertext,
        hash,
        mgf1_hash,
        label,
        any::functions(detected()).1,
    )
}

/// `f`, a `vg_rsa_oaep_decrypt` that this CPU can run, with the hash
/// functions `hash` and `mgf1_hash`, which `supported` accepts.
fn decrypt_with(
    key: &PrivateKey,
    ciphertext: &[u8],
    hash: Hash,
    mgf1_hash: Hash,
    label: &[u8],
    f: DecryptAnyFn,
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
    // they are distinct Rust allocations; `hash` and `mgf1_hash` are SHA-1
    // or SHA-2, whose numbers are in 1..=7; `PrivateKey::from_crt` and the
    // check above give `64 ≤ n_len ≤ 1024`, `out_len = ct_len = n_len`,
    // `1 ≤ e_len ≤ 5 ≤ n_len`, `1 ≤ p_len < n_len`, `1 ≤ q_len < n_len`,
    // `dp_len = qinv_len = p_len`, `dq_len = q_len` and
    // `scratch_len = 16 n_len + 1056`; and the CPU has the features of `f`,
    // which `any::functions` chose for the features detected (its
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
            hash as usize,
            mgf1_hash as usize,
        )
    };
    decrypted(out, len, r)
}

/// The result of a decryption that wrote `out` and `len` and returned `r`.
fn decrypted(mut out: Vec<u8>, len: [u64; 1], r: u32) -> Result<Vec<u8>, Error> {
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
                assert_eq!(supported(h, g), ok);
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
