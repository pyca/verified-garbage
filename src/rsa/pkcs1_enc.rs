//! RSAES-PKCS1-v1_5 (RFC 8017 §7.2), with the implicit rejection of
//! draft-irtf-cfrg-rsa-guidance-10 §7.2: the types of
//! [`PublicKey::encrypt_pkcs1v15`] and [`PrivateKey::decrypt_pkcs1v15`].
//!
//! **RSAES-PKCS1-v1_5 is deprecated** (RFC 8017, draft-irtf-cfrg-rsa-guidance):
//! new protocols should use RSAES-OAEP, or better, a key encapsulation
//! mechanism. [`PrivateKey::decrypt_pkcs1v15`] **never reports an invalid
//! padding**: it returns, instead, a message derived from the private key and
//! the ciphertext, the same each time, which looks random to anyone without
//! the key. So a successful decryption does not prove the ciphertext genuine,
//! and the caller must check the message (its length, and its contents if it
//! can) in constant time. Decryption's timing does not depend on whether the
//! padding is valid, on the message's length, or on which of the two messages
//! it returns.

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

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use crate::arch::dispatch::rsa_pkcs1_enc::{
    vg_rsa_pkcs1_decrypt_auto, vg_rsa_pkcs1_encrypt_random_auto,
};
use crate::entropy::{self, Step, Stop};
use crate::rsa::{PrivateKey, PublicKey, public_scratch_words, scratch_words};
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
            Error::MessageTooLong => "RSA PKCS #1 v1.5 message too long for the modulus",
            Error::InvalidLength => "RSA ciphertext length is not the modulus length",
            Error::InputOutOfRange => "RSA ciphertext is not less than the modulus",
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

impl PublicKey {
    /// RSAES-PKCS1-V1_5-ENCRYPT (RFC 8017 §7.2.1): encrypts `plaintext`, of at
    /// most [`modulus_len`](PublicKey::modulus_len)` - 11` bytes, with `key`,
    /// with a padding string of random nonzero bytes, and returns the
    /// ciphertext ([`modulus_len`](PublicKey::modulus_len) bytes, big-endian).
    /// The timing may depend on the public key, the plaintext's length and
    /// which of the random bytes drawn were zero, not on the plaintext's
    /// contents or the padding string.
    ///
    /// RSAES-PKCS1-v1_5 is deprecated (see the [module](self) documentation).
    pub fn encrypt_pkcs1v15(&self, plaintext: &[u8]) -> Result<Vec<u8>, Error> {
        self.encrypt_pkcs1v15_from(plaintext, os_random)
    }

    /// [`encrypt_pkcs1v15`](Self::encrypt_pkcs1v15), with the random bytes
    /// its padding string is drawn from given by `random`.
    fn encrypt_pkcs1v15_from(
        &self,
        plaintext: &[u8],
        random: impl FnMut(&mut [u8]) -> Result<(), Error>,
    ) -> Result<Vec<u8>, Error> {
        // The plaintext and the padding string are secret.
        crate::dit::enter!(dit);
        let k = self.modulus_len();
        if plaintext.len() + 11 > k {
            return Err(Error::MessageTooLong);
        }
        let mut out = vec![0u8; k];
        let mut scratch = vec![0u64; public_scratch_words(k)];
        let pre = self.pre(dit, &mut scratch);
        let mut status = 0;
        // The padding string needs at least as many random bytes as it has;
        // 32 more make a tape too short for it (more than 32 of at most 1045
        // uniform bytes zero) all but impossible, sparing a second step.
        let drawn = entropy::serve(k - plaintext.len() - 3 + 32, random, |tape| {
            let mut counts = [0u64; 2];
            // SAFETY: each pointer is valid for its length (`out`, `counts`
            // and `scratch` for writes), and none overlaps another or wraps
            // around, as they are distinct Rust allocations; `PublicKey::new`
            // and the check above give `64 ≤ n_len ≤ 1024`, `out_len = n_len`,
            // `1 ≤ e_len ≤ 5 ≤ n_len`, `msg_len + 11 ≤ n_len` and
            // `scratch_len = 8 ⌈n_len / 8⌉ + 48`; `entropy::serve` gives a tape
            // of fresh random bytes, extended only as the function asks, so of
            // at most its budget, `n_len - msg_len + 125` bytes; `pre` holds
            // the verified precomputation for `self.n`, with `2 ⌈n_len / 8⌉`
            // words; and the dispatcher calls only an implementation the CPU
            // has the features of.
            status = unsafe {
                vg_rsa_pkcs1_encrypt_random_auto(
                    dit,
                    out.as_mut_ptr(),
                    k,
                    &mut counts,
                    self.n.as_ptr(),
                    k,
                    self.e.as_ptr(),
                    self.e.len(),
                    plaintext.as_ptr(),
                    plaintext.len(),
                    tape.as_ptr(),
                    tape.len(),
                    scratch.as_mut_ptr(),
                    scratch.len(),
                    pre.as_ptr(),
                    pre.len(),
                )
            };
            match status {
                // The tape has too few nonzero bytes: it consumed none of
                // them and asks for a longer tape.
                0 => Step::More {
                    used: counts[0] as usize,
                    requested: counts[1] as usize,
                },
                1 => Step::Done,
                _ => Step::Failed,
            }
        });
        // The working space holds powers of the encoded message.
        zeroize(&mut scratch);
        match drawn {
            Ok(()) => Ok(out),
            Err(Stop::Fill(e)) => Err(e),
            Err(Stop::Failed) => {
                // `PublicKey::new` checked `n` and `e`, so the tape's whole
                // budget had too few nonzero bytes.
                assert_eq!(status, 3, "encryption refused a valid key");
                Err(Error::Randomness)
            }
        }
    }
}

impl PrivateKey {
    /// RSAES-PKCS1-V1_5-DECRYPT (RFC 8017 §7.2.2) with implicit rejection
    /// (draft-irtf-cfrg-rsa-guidance-10 §7.2): decrypts `ciphertext`
    /// ([`modulus_len`](PrivateKey::modulus_len) bytes, big-endian) with `key`,
    /// and returns the message: the encoded one if its padding is valid, and
    /// otherwise one derived from `d` and the ciphertext, of at most
    /// [`modulus_len`](PrivateKey::modulus_len)` - 11` bytes. **An invalid
    /// padding is never an error** (see the [module](self) documentation): the
    /// errors are a ciphertext of the wrong length or not below the modulus,
    /// and a fault of the private-key operation. The timing may depend on the
    /// public key and the lengths of the primes, not on the ciphertext, the
    /// private key, the validity of the padding or the message (but for the
    /// length of the message returned).
    ///
    /// RSAES-PKCS1-v1_5 is deprecated (see the [module](self) documentation).
    pub fn decrypt_pkcs1v15(&self, ciphertext: &[u8]) -> Result<Vec<u8>, Error> {
        crate::dit::enter!(dit);
        let k = self.modulus_len();
        if ciphertext.len() != k {
            return Err(Error::InvalidLength);
        }
        // Loading the key checked that `0 < d < n` (`RSA_check_key`), and
        // holds it in `n_len` bytes.
        let d = &self.d;
        let mut out = vec![0u8; k];
        let mut len = [0u64; 1];
        let mut scratch = crate::rsa::Scratch::new(scratch_words(k));
        // SAFETY: each pointer is valid for its length (`out`, `len` and
        // `scratch` for writes), and none overlaps another or wraps around, as
        // they are distinct Rust allocations; loading the key and the check
        // above give `64 ≤ n_len ≤ 1024`, `out_len = input_len = n_len`,
        // `1 ≤ e_len ≤ 5 ≤ n_len`, `d_len = n_len`, `1 ≤ p_len < n_len`,
        // `1 ≤ q_len < n_len`, `dp_len = qinv_len = p_len`, `dq_len = q_len`
        // and `scratch_len = 16 n_len + 32`; and the dispatcher calls only an
        // implementation the CPU has the features of.
        let r = unsafe {
            vg_rsa_pkcs1_decrypt_auto(
                dit,
                out.as_mut_ptr(),
                k,
                &mut len,
                self.n.as_ptr(),
                k,
                self.e.as_ptr(),
                self.e.len(),
                d.as_ptr(),
                d.len(),
                ciphertext.as_ptr(),
                k,
                self.p.as_ptr(),
                self.p.len(),
                self.q.as_ptr(),
                self.q.len(),
                self.dp.as_ptr(),
                self.dp.len(),
                self.dq.as_ptr(),
                self.dq.len(),
                self.qinv.as_ptr(),
                self.qinv.len(),
                scratch.as_mut_ptr(),
                scratch.len(),
            )
        };
        // `PrivateKey::from_crt` checked `n`, `e` and the self, so a refusal
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
}

#[cfg(test)]
mod tests {
    use super::{Error, Vec, os_random, vec};
    use crate::rsa::tests::composite_key;
    use alloc::string::ToString;

    /// With `composite_key`'s key, whose factors are not prime, the result
    /// for 2 fails its check against `e`.
    #[test]
    fn decrypt_fault() {
        let (private, _) = composite_key();
        let mut two = vec![0; 64];
        two[63] = 2;
        assert_eq!(private.decrypt_pkcs1v15(&two), Err(Error::Fault));
    }

    /// The same padding string gives the same ciphertext, as the fixed-tape
    /// benchmark relies on.
    #[test]
    fn encryption_from_a_fixed_tape_is_deterministic() {
        let (_, public) = composite_key();
        let encrypt = |byte| {
            public
                .encrypt_pkcs1v15_from(&[7; 53], |buf| {
                    buf.fill(byte);
                    Ok(())
                })
                .unwrap()
        };
        assert_eq!(encrypt(1), encrypt(1));
        assert_ne!(encrypt(1), encrypt(2));
    }

    /// A tape with too few nonzero bytes is extended, keeping its
    /// unconsumed bytes, until the padding string is drawn; a tape of the
    /// whole budget with too few gives up; and a failing random number
    /// generator fails the encryption.
    #[test]
    fn padding_from_tape() {
        let (_, public) = composite_key();
        // The padding string has 8 bytes. The first tape, of 40, is all
        // zeros, and so are the first 4 bytes of the next, of 48: the tape is
        // extended by 8, then by the 4 it still lacks, and the padding string
        // is the ones that follow, as from a tape of ones.
        let mut fills = Vec::new();
        let mut zeros = 44;
        let extended = public
            .encrypt_pkcs1v15_from(&[7; 53], |buf| {
                fills.push(buf.len());
                for b in buf {
                    *b = if zeros > 0 { 0 } else { 1 };
                    zeros -= usize::from(zeros > 0);
                }
                Ok(())
            })
            .unwrap();
        assert_eq!(fills, [40, 8, 4]);
        let ones = public
            .encrypt_pkcs1v15_from(&[7; 53], |buf| {
                buf.fill(1);
                Ok(())
            })
            .unwrap();
        assert_eq!(extended, ones);
        let mut drawn = 0;
        let r = public.encrypt_pkcs1v15_from(&[7; 53], |buf| {
            drawn += buf.len();
            buf.fill(0);
            Ok(())
        });
        assert_eq!(r, Err(Error::Randomness));
        assert_eq!(drawn, 8 + 128);
        assert_eq!(
            public.encrypt_pkcs1v15_from(&[7; 53], |_| Err(Error::Randomness)),
            Err(Error::Randomness)
        );
        assert_eq!(
            public.encrypt_pkcs1v15_from(&[7; 54], |_| Ok(())),
            Err(Error::MessageTooLong)
        );
        let mut ps = [0u8; 64];
        os_random(&mut ps).unwrap();
    }

    #[test]
    fn errors_display() {
        for e in [
            Error::MessageTooLong,
            Error::InvalidLength,
            Error::InputOutOfRange,
            Error::Fault,
            Error::Randomness,
        ] {
            assert!(!e.to_string().is_empty());
        }
    }
}
