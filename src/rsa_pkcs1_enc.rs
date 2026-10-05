//! RSAES-PKCS1-v1_5 encryption and decryption (RFC 8017 §7.2), with the
//! implicit rejection of draft-irtf-cfrg-rsa-guidance-10 §7.2.
//!
//! **RSAES-PKCS1-v1_5 is deprecated.** RFC 8017 keeps it only for
//! compatibility with existing applications, and draft-irtf-cfrg-rsa-guidance
//! recommends against it in new protocols: use RSAES-OAEP, or better, a key
//! encapsulation mechanism, instead. It is here for interoperating with
//! protocols and data that require it.
//!
//! [`encrypt`] is the verified `vg_rsa_pkcs1_encrypt` (contract
//! `VG.Spec.RsaPkcs1Enc.encryptContract`), with a padding string of nonzero
//! bytes from the operating system's generator; it encrypts the encoded
//! message with `vg_rsa_public_checked`.
//!
//! [`decrypt`] is the verified `vg_rsa_pkcs1_decrypt` (contract
//! `VG.Spec.RsaPkcs1Enc.decryptContract`), which computes the encoded
//! message with `vg_rsa_private_checked`, as
//! [`PrivateKey::private_op`] does, and **never reports an invalid
//! padding**: for a ciphertext whose padding is not valid it returns a
//! message derived from the private exponent `d` and the ciphertext (with
//! SHA-256 and HMAC-SHA-256), which is the same every time the same key
//! decrypts the same ciphertext and looks random to anyone without the key.
//! So an attacker learns nothing from which ciphertexts decrypt, a
//! protocol using it must not treat a successful decryption as proof that
//! the ciphertext is genuine, and must check the message (its length, and
//! its contents if it can) in constant time. Whether the padding is valid,
//! the length of the message and which of the two messages is returned do
//! not affect the timing of the verified function. On a CPU with the SHA
//! extensions or AVX2, and with BMI2 and ADX (and AVX512_IFMA), it uses the
//! faster SHA-256 compression functions and private-key operations, as
//! [`hashes::sha256`](crate::hashes::sha256) and [`rsa`](crate::rsa) do.
//!
//! This module only checks the lengths, draws the padding string and
//! allocates the memory the functions work in.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use crate::arch::rsa_pkcs1_enc::{
    vg_rsa_pkcs1_decrypt, vg_rsa_pkcs1_decrypt_crt_adx, vg_rsa_pkcs1_decrypt_crt_ifma,
    vg_rsa_pkcs1_decrypt_sha256_avx2, vg_rsa_pkcs1_decrypt_sha256_avx2_crt_adx,
    vg_rsa_pkcs1_decrypt_sha256_avx2_crt_ifma, vg_rsa_pkcs1_decrypt_sha256_shani,
    vg_rsa_pkcs1_decrypt_sha256_shani_crt_adx, vg_rsa_pkcs1_decrypt_sha256_shani_crt_ifma,
    vg_rsa_pkcs1_encrypt,
};
use crate::cpu::detected;
use crate::hashes::sha256::Sha256Backend;
use crate::rsa::{Backend, PrivateKey, PublicKey, scratch_words, trim};
use crate::zeroize::zeroize;

/// Why an encryption or a decryption was refused. An invalid padding is
/// never one of them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The message is longer than the modulus' length less 11 bytes.
    MessageTooLong,
    /// The ciphertext is not as long as the modulus.
    InvalidLength,
    /// The ciphertext, as a number, is not less than the modulus.
    InputOutOfRange,
    /// The private exponent `d` is zero or longer than the modulus.
    InvalidPrivateKey,
    /// The private-key operation's result failed its check against the
    /// public exponent (see [`rsa::Error::Fault`](crate::rsa::Error::Fault)).
    Fault,
    /// The operating system's random number generator failed.
    Randomness,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::MessageTooLong => "RSA PKCS #1 v1.5 message too long for the modulus",
            Error::InvalidLength => "RSA ciphertext length is not the modulus length",
            Error::InputOutOfRange => "RSA ciphertext is not less than the modulus",
            Error::InvalidPrivateKey => "invalid RSA private exponent",
            Error::Fault => {
                "RSA private-key operation failed its check against the public exponent"
            }
            Error::Randomness => "the random number generator failed",
        })
    }
}

impl core::error::Error for Error {}

/// Fills `ps` with nonzero bytes from `draw`, which fills a buffer with
/// random bytes: all at once, then each zero byte again until it is not.
fn fill_nonzero(
    ps: &mut [u8],
    mut draw: impl FnMut(&mut [u8]) -> Result<(), Error>,
) -> Result<(), Error> {
    draw(ps)?;
    for b in ps.iter_mut() {
        while *b == 0 {
            draw(core::slice::from_mut(b))?;
        }
    }
    Ok(())
}

/// The operating system's random bytes.
fn os_random(buf: &mut [u8]) -> Result<(), Error> {
    getrandom::fill(buf).map_err(|_| Error::Randomness)
}

/// RSAES-PKCS1-V1_5-ENCRYPT (RFC 8017 §7.2.1): encrypts `plaintext`, of at
/// most [`modulus_len`](PublicKey::modulus_len)` - 11` bytes, with `key`,
/// with a padding string of random nonzero bytes, and returns the
/// ciphertext ([`modulus_len`](PublicKey::modulus_len) bytes, big-endian).
/// The timing may depend on the public key and the plaintext's length, not
/// on its contents.
///
/// RSAES-PKCS1-v1_5 is deprecated (see the [module](self) documentation).
pub fn encrypt(key: &PublicKey, plaintext: &[u8]) -> Result<Vec<u8>, Error> {
    let k = key.modulus_len();
    if plaintext.len() + 11 > k {
        return Err(Error::MessageTooLong);
    }
    let mut ps = vec![0u8; k - plaintext.len() - 3];
    fill_nonzero(&mut ps, os_random)?;
    let c = encrypt_with(key, plaintext, &ps);
    zeroize(&mut ps);
    Ok(c)
}

/// `vg_rsa_pkcs1_encrypt` of `plaintext` with the padding string `ps`, of
/// `k - plaintext.len() - 3` nonzero bytes.
fn encrypt_with(key: &PublicKey, plaintext: &[u8], ps: &[u8]) -> Vec<u8> {
    let k = key.modulus_len();
    let mut out = vec![0u8; k];
    let mut scratch = vec![0u64; scratch_words(k)];
    // SAFETY: each pointer is valid for its length (`out` and `scratch` for
    // writes), and none overlaps another or wraps around, as they are
    // distinct Rust allocations; `PublicKey::new` and `encrypt` give
    // `64 ≤ n_len ≤ 1024`, `out_len = n_len`, `1 ≤ e_len ≤ 5 ≤ n_len`,
    // `msg_len + 11 ≤ n_len`, `ps_len = n_len - msg_len - 3` and
    // `scratch_len = 16 n_len`. It needs no CPU feature.
    let r = unsafe {
        vg_rsa_pkcs1_encrypt(
            out.as_mut_ptr(),
            k,
            key.n.as_ptr(),
            k,
            key.e.as_ptr(),
            key.e.len(),
            plaintext.as_ptr(),
            plaintext.len(),
            ps.as_ptr(),
            ps.len(),
            scratch.as_mut_ptr(),
            scratch.len(),
        )
    };
    // The working space holds powers of the encoded message.
    zeroize(&mut scratch);
    // `PublicKey::new` checked `n` and `e`, and `PS` has no zero byte.
    assert_eq!(r, 1, "vg_rsa_pkcs1_encrypt refused a valid key and padding");
    out
}

/// The type of the implementations of `vg_rsa_pkcs1_decrypt`.
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

/// The implementation of `vg_rsa_pkcs1_decrypt` for the implementations of
/// SHA-256 and of the private-key operation chosen.
fn decrypt_fn(sha: Sha256Backend, crt: Backend) -> DecryptFn {
    match (sha, crt) {
        (Sha256Backend::Scalar, Backend::Baseline) => vg_rsa_pkcs1_decrypt,
        (Sha256Backend::Scalar, Backend::Adx) => vg_rsa_pkcs1_decrypt_crt_adx,
        (Sha256Backend::Scalar, Backend::Ifma) => vg_rsa_pkcs1_decrypt_crt_ifma,
        (Sha256Backend::ShaNi, Backend::Baseline) => vg_rsa_pkcs1_decrypt_sha256_shani,
        (Sha256Backend::ShaNi, Backend::Adx) => vg_rsa_pkcs1_decrypt_sha256_shani_crt_adx,
        (Sha256Backend::ShaNi, Backend::Ifma) => vg_rsa_pkcs1_decrypt_sha256_shani_crt_ifma,
        (Sha256Backend::Avx2, Backend::Baseline) => vg_rsa_pkcs1_decrypt_sha256_avx2,
        (Sha256Backend::Avx2, Backend::Adx) => vg_rsa_pkcs1_decrypt_sha256_avx2_crt_adx,
        (Sha256Backend::Avx2, Backend::Ifma) => vg_rsa_pkcs1_decrypt_sha256_avx2_crt_ifma,
    }
}

/// RSAES-PKCS1-V1_5-DECRYPT (RFC 8017 §7.2.2) with implicit rejection
/// (draft-irtf-cfrg-rsa-guidance-10 §7.2): decrypts `ciphertext`
/// ([`modulus_len`](PrivateKey::modulus_len) bytes, big-endian) with `key`,
/// and returns the message: the encoded one if its padding is valid, and
/// otherwise one derived from `d` and the ciphertext, of at most
/// [`modulus_len`](PrivateKey::modulus_len)` - 11` bytes. **An invalid
/// padding is never an error** (see the [module](self) documentation): the
/// errors are a ciphertext of the wrong length or not below the modulus, a
/// private exponent of no valid length, and a fault of the private-key
/// operation. The timing may depend on the public key and the lengths of
/// the primes, not on the ciphertext, the private key, the validity of the
/// padding or the message (but for the length of the message returned).
///
/// RSAES-PKCS1-v1_5 is deprecated (see the [module](self) documentation).
pub fn decrypt(key: &PrivateKey, ciphertext: &[u8]) -> Result<Vec<u8>, Error> {
    let k = key.modulus_len();
    if ciphertext.len() != k {
        return Err(Error::InvalidLength);
    }
    let d = trim(&key.d);
    if d.is_empty() || d.len() > k {
        return Err(Error::InvalidPrivateKey);
    }
    let f = decrypt_fn(
        Sha256Backend::select(detected()),
        Backend::select(detected()),
    );
    let mut out = vec![0u8; k];
    let mut len = [0u64; 1];
    let mut scratch = vec![0u64; scratch_words(k)];
    // SAFETY: each pointer is valid for its length (`out`, `len` and
    // `scratch` for writes), and none overlaps another or wraps around, as
    // they are distinct Rust allocations; `PrivateKey::from_crt` and the
    // checks above give `64 ≤ n_len ≤ 1024`, `out_len = input_len = n_len`,
    // `1 ≤ e_len ≤ 5 ≤ n_len`, `1 ≤ d_len ≤ n_len`, `1 ≤ p_len < n_len`,
    // `1 ≤ q_len < n_len`, `dp_len = qinv_len = p_len`, `dq_len = q_len`
    // and `scratch_len = 16 n_len`; and the CPU has the features of the
    // implementations of SHA-256 and of the private-key operation that
    // `Sha256Backend::select` and `Backend::select` chose, which are those
    // of `f`.
    let r = unsafe {
        f(
            out.as_mut_ptr(),
            k,
            &mut len,
            key.n.as_ptr(),
            k,
            key.e.as_ptr(),
            key.e.len(),
            d.as_ptr(),
            d.len(),
            ciphertext.as_ptr(),
            k,
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
            scratch.as_mut_ptr(),
            scratch.len(),
        )
    };
    // The working space holds the private key, `D`, `KDK` and the
    // alternative message.
    zeroize(&mut scratch);
    // `PrivateKey::from_crt` checked `n`, `e` and the key, so a refusal
    // means the ciphertext is not below the modulus.
    match r {
        1 => {
            // The function returns at most `n_len - 11` bytes.
            let l = len[0] as usize;
            out.drain(..k - l);
            Ok(out)
        }
        2 => Err(Error::Fault),
        _ => Err(Error::InputOutOfRange),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::ToString;

    #[test]
    fn nonzero_padding() {
        // Zeros come back from the first draw at the first, second and last
        // bytes, and again from the second draw of the first byte.
        let mut draws = 0;
        let mut ps = [0u8; 5];
        fill_nonzero(&mut ps, |buf| {
            draws += 1;
            match draws {
                1 => buf.copy_from_slice(&[0, 0, 7, 9, 0]),
                2 => buf[0] = 0,
                _ => buf[0] = draws,
            }
            Ok(())
        })
        .unwrap();
        assert_eq!(ps, [3, 4, 7, 9, 5]);
        assert_eq!(
            fill_nonzero(&mut ps, |_| Err(Error::Randomness)),
            Err(Error::Randomness)
        );
        let mut ps = [0u8; 2];
        let mut first = true;
        let r = fill_nonzero(&mut ps, |buf| {
            if first {
                first = false;
                buf.fill(0);
                Ok(())
            } else {
                Err(Error::Randomness)
            }
        });
        assert_eq!(r, Err(Error::Randomness));
        let mut ps = [0u8; 64];
        os_random(&mut ps).unwrap();
    }

    /// Every pair of implementations has its instance (each is tested end
    /// to end on a CPU that chooses it).
    #[test]
    fn rsa_pkcs1_backends() {
        let mut fns = Vec::new();
        for sha in [
            Sha256Backend::Scalar,
            Sha256Backend::ShaNi,
            Sha256Backend::Avx2,
        ] {
            for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
                fns.push(decrypt_fn(sha, crt) as usize);
            }
        }
        fns.sort_unstable();
        fns.dedup();
        assert_eq!(fns.len(), 9);
    }

    #[test]
    fn errors_display() {
        for e in [
            Error::MessageTooLong,
            Error::InvalidLength,
            Error::InputOutOfRange,
            Error::InvalidPrivateKey,
            Error::Fault,
            Error::Randomness,
        ] {
            assert!(!e.to_string().is_empty());
        }
    }
}
