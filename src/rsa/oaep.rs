//! RSAES-OAEP (RFC 8017 §7.1), with SHA-1 or a SHA-2 hash function for the
//! label and for MGF1: the types of [`PublicKey::encrypt_oaep`] and
//! [`PrivateKey::decrypt_oaep`].
//!
//! Every decryption failure is the one error [`Error::Decryption`], and
//! decryption's timing does not depend on whether the decoding succeeded, nor
//! on where the message starts or its length.

#![cfg(all(
    any(
        target_arch = "x86",
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64",
        target_arch = "riscv64"
    ),
    feature = "alloc"
))]

mod table;

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use crate::arch::dispatch::rsa_oaep::{
    vg_rsa_oaep_decrypt_auto, vg_rsa_oaep_encrypt_precomputed_auto,
};
pub use crate::rsa::pkcs1_sig::Hash;
use crate::rsa::{PrivateKey, PublicKey};
use crate::zeroize::zeroize;

/// Why an encryption or a decryption was refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// A hash function is not one this module supports.
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
    /// public exponent (a factor of the key is not prime, or the computation
    /// was faulted) and is not released.
    Fault,
    /// The operating system's random number generator failed.
    Randomness,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::UnsupportedHash => "unsupported hash function for RSA OAEP",
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

/// The words of working space encryption needs for an `n_len`-byte modulus
/// (`VG.Spec.RsaPss.publicScratchWords`, which OAEP's contracts share).
fn public_scratch_words(n_len: usize) -> usize {
    crate::rsa::public_scratch_words(n_len) + 1024
}

/// The words of working space decryption needs for an `n_len`-byte modulus
/// (`VG.Spec.RsaPss.scratchWords`, which OAEP's contracts share).
fn scratch_words(n_len: usize) -> usize {
    crate::rsa::scratch_words(n_len) + 1024
}

/// A hash function, as the verified functions take it, their last two
/// arguments (the label's hash function's, then MGF1's): the words of one of
/// the tables of `Hash` (`crate::arch::fn_tables`).
type Table = *const [usize; 5];

/// The tables of the label's hash function `hash` and of MGF1's `mgf1_hash`
/// (`table::table`), or `None` if this module does not support them.
fn with_tables(hash: Hash, mgf1_hash: Hash) -> Option<(Table, Table)> {
    Some((table::table(hash)?, table::table(mgf1_hash)?))
}

impl PublicKey {
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
    pub fn encrypt_oaep(
        &self,
        plaintext: &[u8],
        hash: Hash,
        mgf1_hash: Hash,
        label: &[u8],
    ) -> Result<Vec<u8>, Error> {
        self.encrypt_oaep_from(plaintext, hash, mgf1_hash, label, os_random)
    }

    /// [`encrypt_oaep`](Self::encrypt_oaep), with its seed drawn from
    /// `random`.
    fn encrypt_oaep_from(
        &self,
        plaintext: &[u8],
        hash: Hash,
        mgf1_hash: Hash,
        label: &[u8],
        random: impl FnMut(&mut [u8]) -> Result<(), Error>,
    ) -> Result<Vec<u8>, Error> {
        let (h, m) = with_tables(hash, mgf1_hash).ok_or(Error::UnsupportedHash)?;
        encrypt_with(self, plaintext, label, (h, hash.digest_len()), m, random)
    }
}

/// `vg_rsa_oaep_encrypt_precomputed` with the label's hash function `hash`
/// (its table and digest length) and MGF1's `mgf1`, and a seed from
/// `random`.
fn encrypt_with(
    key: &PublicKey,
    plaintext: &[u8],
    label: &[u8],
    (hash, len): (Table, usize),
    mgf1: Table,
    mut random: impl FnMut(&mut [u8]) -> Result<(), Error>,
) -> Result<Vec<u8>, Error> {
    // The plaintext and the seed are secret.
    crate::dit::enter!(dit);
    let k = key.modulus_len();
    if plaintext.len() + 2 * len + 2 > k {
        return Err(Error::MessageTooLong);
    }
    // The hash functions' digests are at most 64 bytes.
    let mut seed = [0u8; 64];
    let seed = &mut seed[..len];
    random(seed)?;
    let mut out = vec![0u8; k];
    let mut scratch = key.verify_scratch.take(public_scratch_words(k), true);
    let pre = key.pre(dit, &mut scratch);
    // SAFETY: each pointer is valid for its length (`out` and `scratch` for
    // writes), and none overlaps another or wraps around, as they are
    // distinct Rust allocations; `PublicKey::new` gives
    // `64 ≤ n_len ≤ 1024`, `1 ≤ e_len ≤ 5 ≤ n_len`, and `out_len = n_len`
    // and `scratch_len = 8 ⌈n_len / 8⌉ + 1072`; `pre` holds the verified
    // precomputation for `key.n`, with `2 * ceil(n_len / 8)` words; `hash`
    // and `mgf1` are the words of tables of the crate's of `Hash`, and
    // `seed_len` is the digest length of `hash`'s, its word 4
    // (`hashes::tables::tests::table_words` checks it); and the dispatchers,
    // the function's and the tables' (`table::table`), call only
    // implementations the CPU has the features of.
    let r = unsafe {
        vg_rsa_oaep_encrypt_precomputed_auto(
            dit,
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
            len,
            scratch.as_mut_ptr(),
            scratch.len(),
            pre.as_ptr(),
            pre.len(),
            hash,
            mgf1,
        )
    };
    // ScratchLease wipes the encoded message and its powers before reuse.
    zeroize(seed);
    // `PublicKey::new` checked `n`, and the message's length is checked
    // above.
    assert_eq!(r, 1, "OAEP encryption refused a valid key and message");
    Ok(out)
}

impl PrivateKey {
    /// RSAES-OAEP-DECRYPT (RFC 8017 §7.1.2) with the hash function `hash` and
    /// MGF1 over `mgf1_hash`: decrypts `ciphertext`
    /// ([`modulus_len`](PrivateKey::modulus_len) bytes, big-endian) with `key`
    /// and the label `label`, and returns the message. A ciphertext not below
    /// the modulus and every failure of its decoding are the one error
    /// [`Error::Decryption`]. The timing may depend on the public key, the
    /// lengths of the primes and of the label, not on the ciphertext, the
    /// private key, the label's contents, whether the decryption succeeds or
    /// the message's length.
    pub fn decrypt_oaep(
        &self,
        ciphertext: &[u8],
        hash: Hash,
        mgf1_hash: Hash,
        label: &[u8],
    ) -> Result<Vec<u8>, Error> {
        crate::dit::enter!(dit);
        let (h, m) = with_tables(hash, mgf1_hash).ok_or(Error::UnsupportedHash)?;
        decrypt_with(dit, self, ciphertext, label, h, m)
    }
}

/// `vg_rsa_oaep_decrypt` with the label's hash function `hash` and MGF1's
/// `mgf1`.
fn decrypt_with(
    dit: crate::dit::Dit<'_>,
    key: &PrivateKey,
    ciphertext: &[u8],
    label: &[u8],
    hash: Table,
    mgf1: Table,
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
    // `scratch_len = 16 n_len + 1056`; `hash` and `mgf1` are the words of
    // tables of the crate's of `Hash`; and the dispatchers, the function's
    // and the tables' (`table::table`), call only implementations the CPU
    // has the features of.
    let r = unsafe {
        vg_rsa_oaep_decrypt_auto(
            dit,
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
            hash,
            mgf1,
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

#[cfg(test)]
mod tests {
    use super::{Error, Hash, vec, with_tables};
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
                let supported = |x| {
                    x != Hash::Md5
                        && !matches!(
                            x,
                            Hash::Sha3_224 | Hash::Sha3_256 | Hash::Sha3_384 | Hash::Sha3_512
                        )
                };
                // Each is any of them (`table::table`).
                let ok = supported(h) && supported(g);
                assert_eq!(with_tables(h, g).is_some(), ok);
                n += usize::from(ok);
            }
        }
        assert_eq!(n, 49);
    }

    #[test]
    fn refused() {
        let (private, public) = composite_key();
        assert_eq!(
            public.encrypt_oaep(b"", Hash::Md5, Hash::Md5, b""),
            Err(Error::UnsupportedHash)
        );
        assert_eq!(
            private.decrypt_oaep(&[0; 64], Hash::Sha256, Hash::Md5, b""),
            Err(Error::UnsupportedHash)
        );
        // 64 bytes hold at most 22 bytes of message with SHA-1, none with
        // SHA-512.
        assert_eq!(
            public.encrypt_oaep(&[0; 23], Hash::Sha1, Hash::Sha1, b""),
            Err(Error::MessageTooLong)
        );
        assert_eq!(
            public.encrypt_oaep(b"", Hash::Sha512, Hash::Sha512, b""),
            Err(Error::MessageTooLong)
        );
        let c = public
            .encrypt_oaep(&[7; 22], Hash::Sha1, Hash::Sha1, b"label")
            .unwrap();
        assert_eq!(c.len(), 64);
        assert_eq!(
            private.decrypt_oaep(&c[1..], Hash::Sha1, Hash::Sha1, b"label"),
            Err(Error::InvalidLength)
        );
        let mut two = vec![0; 64];
        two[63] = 2;
        assert_eq!(
            private.decrypt_oaep(&two, Hash::Sha1, Hash::Sha1, b""),
            Err(Error::Fault)
        );
        // Not below the modulus.
        assert_eq!(
            private.decrypt_oaep(&[0xff; 64], Hash::Sha1, Hash::Sha1, b""),
            Err(Error::Decryption)
        );
    }

    /// The same seed gives the same ciphertext, as the fixed-tape benchmark
    /// relies on, and a failing draw fails the encryption.
    #[test]
    fn encryption_from_a_fixed_tape_is_deterministic() {
        let (_, public) = composite_key();
        let encrypt = |byte| {
            public.encrypt_oaep_from(&[7; 22], Hash::Sha1, Hash::Sha1, b"", |buf| {
                buf.fill(byte);
                Ok(())
            })
        };
        assert_eq!(encrypt(1), encrypt(1));
        assert_ne!(encrypt(1), encrypt(2));
        assert_eq!(
            public.encrypt_oaep_from(b"", Hash::Sha1, Hash::Sha1, b"", |_| {
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
