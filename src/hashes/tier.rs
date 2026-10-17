//! The tiers of implementations of the Merkle–Damgård hash functions: for
//! the verified functions that take the hash function as an argument (by
//! its number, `VG.Spec.HashId`), and so call, of each hash function, the
//! implementation of their tier (`Proof/Pbkdf2/Md/<Target>/Tier.lean`,
//! `Variants/MdHashTier/<Target>/`).
//!
//! A CPU's tier is the one whose implementations of SHA-1's, SHA-256's and
//! SHA-512's compression functions are those the hash functions of
//! [`hashes`](super) choose on it ([`Tier::select`]); a CPU that no tier
//! matches (one with SHA-512's but not SHA-256's faster code, which no CPU
//! is) gets the fastest tier it can run.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
// The functions that take the hash function as an argument use it.
#![cfg_attr(not(test), allow(dead_code))]

use super::sha1::Sha1Backend;
use super::sha256::Sha256Backend;
use super::sha512::Sha512Backend;
use crate::cpu::Features;

/// A tier: the suffix of the names of the functions made with it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Tier {
    /// Every compression function in scalar code.
    Base,
    /// SHA-256's and SHA-512's with AVX2, SHA-1's in scalar code (`_avx2`).
    #[cfg(target_arch = "x86_64")]
    Avx2,
    /// SHA-1's and SHA-256's with the SHA extensions, SHA-512's in scalar
    /// code (`_shani`).
    #[cfg(target_arch = "x86_64")]
    ShaNi,
    /// SHA-1's and SHA-256's with the SHA extensions, SHA-512's with AVX2
    /// (`_shani_avx2`).
    #[cfg(target_arch = "x86_64")]
    ShaNiAvx2,
    /// SHA-1's and SHA-256's with the SHA extensions, SHA-512's with the
    /// SHA512 instructions (`_shani_sha512`).
    #[cfg(target_arch = "x86_64")]
    ShaNiSha512,
    /// SHA-1's and SHA-256's with the SHA-1 and SHA-256 instructions,
    /// SHA-512's in scalar code (`_sha2`).
    #[cfg(target_arch = "aarch64")]
    Sha2,
    /// SHA-1's and SHA-256's with the SHA-1 and SHA-256 instructions,
    /// SHA-512's with the SHA-512 instructions (`_sha2_sha3`).
    #[cfg(target_arch = "aarch64")]
    Sha2Sha3,
}

impl Tier {
    /// The tier of a CPU with the features `f`.
    pub(crate) fn select(f: Features) -> Self {
        Self::of(
            Sha1Backend::select(f),
            Sha256Backend::select(f),
            Sha512Backend::select(f),
        )
    }

    /// The tier of the implementations the hash functions choose.
    fn of(sha1: Sha1Backend, sha256: Sha256Backend, sha512: Sha512Backend) -> Self {
        #[cfg(target_arch = "x86_64")]
        return match (sha1, sha256, sha512) {
            (Sha1Backend::ShaNi, Sha256Backend::ShaNi, Sha512Backend::ShaNi) => Self::ShaNiSha512,
            (Sha1Backend::ShaNi, Sha256Backend::ShaNi, Sha512Backend::Avx2) => Self::ShaNiAvx2,
            (Sha1Backend::ShaNi, Sha256Backend::ShaNi, _) => Self::ShaNi,
            (_, Sha256Backend::Avx2, Sha512Backend::Avx2 | Sha512Backend::ShaNi) => Self::Avx2,
            _ => Self::Base,
        };
        #[cfg(target_arch = "aarch64")]
        return match (sha1, sha256, sha512) {
            (Sha1Backend::Sha2, Sha256Backend::Sha2, Sha512Backend::Sha3) => Self::Sha2Sha3,
            (Sha1Backend::Sha2, Sha256Backend::Sha2, _) => Self::Sha2,
            _ => Self::Base,
        };
    }
}

#[cfg(test)]
mod tests {
    use super::{Sha1Backend, Sha256Backend, Sha512Backend, Tier};
    use crate::cpu::detected;

    #[test]
    fn select() {
        assert_eq!(
            Tier::select(detected()),
            Tier::of(
                Sha1Backend::select(detected()),
                Sha256Backend::select(detected()),
                Sha512Backend::select(detected())
            )
        );
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn of() {
        use Sha1Backend as A;
        use Sha256Backend as B;
        use Sha512Backend as C;
        for (a, b, c, t) in [
            (A::ShaNi, B::ShaNi, C::ShaNi, Tier::ShaNiSha512),
            (A::ShaNi, B::ShaNi, C::Avx2, Tier::ShaNiAvx2),
            (A::ShaNi, B::ShaNi, C::Scalar, Tier::ShaNi),
            (A::Scalar, B::Avx2, C::Avx2, Tier::Avx2),
            (A::Scalar, B::Avx2, C::ShaNi, Tier::Avx2),
            (A::Scalar, B::Scalar, C::ShaNi, Tier::Base),
            (A::Scalar, B::Scalar, C::Scalar, Tier::Base),
        ] {
            assert_eq!(Tier::of(a, b, c), t);
        }
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn of() {
        use Sha1Backend as A;
        use Sha256Backend as B;
        use Sha512Backend as C;
        for (a, b, c, t) in [
            (A::Sha2, B::Sha2, C::Sha3, Tier::Sha2Sha3),
            (A::Sha2, B::Sha2, C::Scalar, Tier::Sha2),
            (A::Scalar, B::Scalar, C::Sha3, Tier::Base),
            (A::Scalar, B::Scalar, C::Scalar, Tier::Base),
        ] {
            assert_eq!(Tier::of(a, b, c), t);
        }
    }
}
