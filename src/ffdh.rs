//! Finite-field Diffie–Hellman, for the component API used by cryptography.
//!
//! Public-key validation and exchange call the verified FFDH operations.
//! Exchange secret exponentiation follows a fixed schedule over the public encoding
//! length supplied at import, or the public sampling bound for generated keys.
//! All domain arithmetic and secret exponentiation run in verified code.
//! Private-key generation samples and validates the scalar in verified code,
//! which also retries rejected attempts and asks for the random bytes they
//! need. Rust obtains random bytes and packs inputs and results. Parameter
//! generation runs entirely in verified code, including its attempt limit
//! and entropy requests; Rust allocates and fills the random tape it asks
//! for. Parameter generation is available on every supported architecture.
//! Imported parameters receive structural and algebraic checks; callers must
//! establish primality/provenance. Optional q enables subgroup checks.
//! Exchange returns exactly ceil(bits(p)/8) bytes, without applying a KDF.

#![cfg(all(
    any(
        target_arch = "x86",
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm",
        all(target_arch = "powerpc64", target_endian = "little")
    ),
    feature = "alloc"
))]

mod arithmetic;
mod domain;
mod generation;
#[cfg(any(target_arch = "arm", target_arch = "aarch64"))]
mod precomputed;
#[cfg(test)]
mod vetted_tests;

use crate::zeroize::zeroize;
use alloc::vec::Vec;
use arithmetic::{canonical, scalar};
use core::fmt;
use domain::Domain;

/// Minimum supported modulus size, including legacy cryptography keys.
pub const MIN_BITS: usize = 512;
/// Maximum supported modulus size, matching the crate's RSA arithmetic bound.
pub const MAX_BITS: usize = 8192;

/// Why an FFDH operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// Invalid modulus, generator, subgroup order or algebraic domain relation.
    InvalidParameters,
    /// Invalid public/private scalar, subgroup membership or key consistency.
    InvalidKey,
    /// The peer belongs to a different domain.
    ParametersMismatch,
    /// A shared value of zero, one or p-1 was computed.
    InvalidSharedSecret,
    /// The operating system's random number generator failed.
    Randomness,
    /// Bounded random sampling or parameter generation exhausted its attempts.
    TooManyIterations,
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::InvalidParameters => "invalid FFDH parameters",
            Self::InvalidKey => "invalid FFDH key",
            Self::ParametersMismatch => "FFDH peer parameters differ",
            Self::InvalidSharedSecret => "invalid FFDH shared secret",
            Self::Randomness => "FFDH random number generator failed",
            Self::TooManyIterations => "too many FFDH generation attempts",
        })
    }
}
impl core::error::Error for Error {}

/// Imported, checked domain components.
#[derive(Clone)]
pub struct Parameters {
    p: Vec<u8>,
    g: Vec<u8>,
    q: Option<Vec<u8>>,
    // The components laid out for the verified operations.
    domain: Domain,
}
impl fmt::Debug for Parameters {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Parameters")
            .field("p", &self.p)
            .field("g", &self.g)
            .field("q", &self.q)
            .finish()
    }
}
impl PartialEq for Parameters {
    fn eq(&self, other: &Self) -> bool {
        self.p == other.p && self.g == other.g && self.q == other.q
    }
}
impl Eq for Parameters {}

impl Parameters {
    /// Import unsigned big-endian p, g and optional q. Leading zeros are
    /// accepted and normalized. Checks 512..=8192 bits, odd p, 1<g<p-1;
    /// with q, also odd 2<q<p-1, q|(p-1) and g^q mod p=1. Does not
    /// primality-test imported parameters.
    ///
    /// On ARMv7 and AArch64, this also initializes reusable public key-generation data
    /// (about 34 times p's byte length). Clones share that allocation.
    pub fn from_components(p: &[u8], g: &[u8], q: Option<&[u8]>) -> Result<Self, Error> {
        let (p, g, q) = (canonical(p), canonical(g), q.map(canonical));
        let domain = Domain::new(p, g, q).ok_or(Error::InvalidParameters)?;
        Ok(Self {
            p: p.to_vec(),
            g: g.to_vec(),
            q: q.map(<[u8]>::to_vec),
            domain,
        })
    }

    /// Generate probable safe-prime parameters of exactly bits bits with
    /// generator 2 or 5. The result omits q, as PKCS #3/OpenSSL does.
    /// Miller–Rabin uses 64 independent uniform witnesses through 2048 bits
    /// and 128 above. There is no primality certificate.
    pub fn generate(bits: usize, generator: u32) -> Result<Self, Error> {
        generation::parameters(bits, generator, getrandom::fill)
    }

    /// [`generate`](Self::generate), with its random bytes drawn from `fill`
    /// instead of the operating system.
    ///
    /// Not part of the API: it lets benchmarks compare implementations on
    /// identical work, from fixed tapes. The parameters are generated as
    /// `generate` documents only if `fill` supplies uniformly random bytes.
    #[doc(hidden)]
    pub fn generate_with_rng<E>(
        bits: usize,
        generator: u32,
        fill: impl FnMut(&mut [u8]) -> Result<(), E>,
    ) -> Result<Self, Error> {
        generation::parameters(bits, generator, fill)
    }

    /// Borrow canonical unsigned big-endian (p,g,q), preserving q's presence.
    pub fn components(&self) -> (&[u8], &[u8], Option<&[u8]>) {
        (&self.p, &self.g, self.q.as_deref())
    }

    /// The bit length of p.
    pub fn key_size(&self) -> usize {
        arithmetic::bits(&self.p)
    }

    /// Generate a private key, rejecting degenerate public values and retrying.
    /// On ARMv7 and AArch64, exact RFC 3526/7919 safe-prime groups with generator 2 use
    /// the RFC 7919 shorter-exponent bounds. Other domains and architectures
    /// sample uniformly in 1..q, or 1..p-1 when q is absent.
    pub fn generate_private_key(&self) -> Result<PrivateKey, Error> {
        self.generate_with(getrandom::fill)
    }

    /// [`generate_private_key`](Self::generate_private_key), with its random
    /// bytes drawn from `fill` instead of the operating system.
    ///
    /// Not part of the API: it lets benchmarks compare implementations on
    /// identical work, from fixed tapes. The key is secret only if `fill`
    /// supplies uniformly random bytes.
    #[doc(hidden)]
    pub fn generate_private_key_with_rng<E>(
        &self,
        fill: impl FnMut(&mut [u8]) -> Result<(), E>,
    ) -> Result<PrivateKey, Error> {
        self.generate_with(fill)
    }

    /// Verified code runs the whole search: it draws and checks each scalar
    /// and its public value, retries up to 128 times for an in-range scalar
    /// and up to 128 times for a public value that is not degenerate, and
    /// asks for the random bytes each attempt needs.
    fn generate_with<E>(
        &self,
        fill: impl FnMut(&mut [u8]) -> Result<(), E>,
    ) -> Result<PrivateKey, Error> {
        let len = self.p.len();
        #[cfg(any(target_arch = "arm", target_arch = "aarch64"))]
        let exponent_len = self.domain.exponent_len();
        #[cfg(not(any(target_arch = "arm", target_arch = "aarch64")))]
        let exponent_len = self.q.as_ref().map_or(len, Vec::len);
        let mut x = alloc::vec![0; len];
        let mut y = alloc::vec![0; len];
        let mut state = self.domain.key_state();
        let result = generation::serve(state[3] as usize, fill, |tape| {
            self.domain.key_search(&mut state, tape, &mut x, &mut y)
        });
        zeroize(&mut state);
        result.map(|()| PrivateKey {
            public: PublicKey {
                params: self.clone(),
                y: canonical(&y).to_vec(),
            },
            x,
            exponent_len,
        })
    }
}

/// An immutable public key with checked range and optional subgroup membership.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicKey {
    params: Parameters,
    y: Vec<u8>,
}
impl PublicKey {
    /// Import an unsigned big-endian y, accepting leading zeros.
    pub fn from_components(params: &Parameters, y: &[u8]) -> Result<Self, Error> {
        let y = canonical(y);
        if !params.domain.check_public(y) {
            return Err(Error::InvalidKey);
        }
        Ok(Self {
            params: params.clone(),
            y: y.to_vec(),
        })
    }
    /// Borrow the domain parameters.
    pub fn parameters(&self) -> &Parameters {
        &self.params
    }
    /// Borrow canonical unsigned big-endian y.
    pub fn component(&self) -> &[u8] {
        &self.y
    }
}

/// A private scalar, held at the modulus' byte width and wiped on drop.
/// Debug output never contains the scalar.
pub struct PrivateKey {
    public: PublicKey,
    x: Vec<u8>,
    // Public input encoding length, capped at the modulus width.
    exponent_len: usize,
}
impl fmt::Debug for PrivateKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PrivateKey")
            .field("public", &self.public)
            .finish_non_exhaustive()
    }
}
impl Drop for PrivateKey {
    fn drop(&mut self) {
        zeroize(&mut self.x);
    }
}
impl PrivateKey {
    /// Import an unsigned big-endian `x`, deriving `y = g^x mod p`.
    /// This accepts private components from PKCS#8, which omits `y`.
    /// Checks the scalar range and the derived public value. Parsing and
    /// the exponentiation schedule follow [`Self::from_components`].
    pub fn from_private_components(params: &Parameters, x: &[u8]) -> Result<Self, Error> {
        let exponent_len = x.len().min(params.p.len());
        let (zeros, scalar) = x.split_at(x.len() - exponent_len);
        if scalar.is_empty() || zeros.iter().any(|&b| b != 0) {
            return Err(Error::InvalidKey);
        }
        let mut y = alloc::vec![0; params.p.len()];
        // One exponentiation checks the scalar range and derives a valid y.
        if params.domain.derive_public(scalar, &mut y) != 1 {
            return Err(Error::InvalidKey);
        }
        Ok(Self::assemble(params, canonical(&y), scalar, exponent_len))
    }

    /// Import y and x with variable-time parsing; check range and y=g^x mod p.
    /// The encoding length of x is public and determines the fixed
    /// exponentiation schedule, capped at the modulus width. Leading zeros
    /// are retained in that schedule; the scalar value does not set its length.
    pub fn from_components(params: &Parameters, y: &[u8], x: &[u8]) -> Result<Self, Error> {
        // Only zeros may precede the modulus' width. Retain the public
        // encoding length, capped at that width, for secret exponentiation.
        let exponent_len = x.len().min(params.p.len());
        let (zeros, x) = x.split_at(x.len() - exponent_len);
        let y = canonical(y);
        if zeros.iter().any(|&b| b != 0) {
            return Err(Error::InvalidKey);
        }
        if !params.domain.check_private(y, x) {
            return Err(Error::InvalidKey);
        }
        Ok(Self::assemble(params, y, x, exponent_len))
    }

    /// The key of a checked pair: canonical `y`, and `x` without the zeros
    /// before its `exponent_len` bytes.
    fn assemble(params: &Parameters, y: &[u8], x: &[u8], exponent_len: usize) -> Self {
        Self {
            public: PublicKey {
                params: params.clone(),
                y: y.to_vec(),
            },
            x: scalar(x, params.p.len()),
            exponent_len,
        }
    }
    /// Borrow the public half of this key.
    pub fn public_key(&self) -> &PublicKey {
        &self.public
    }
    /// Borrow the private component at p's byte width. The caller must wipe
    /// any copy it makes of this scalar.
    pub fn private_component(&self) -> &[u8] {
        &self.x
    }
    /// Compute y_peer^x mod p. Returns a modulus-width big-endian value;
    /// rejects mismatched domains and degenerate shared values. Caller owns
    /// and is responsible for wiping the returned shared secret.
    pub fn exchange(&self, peer: &PublicKey) -> Result<Vec<u8>, Error> {
        let params = &self.public.params;
        if params != &peer.params {
            return Err(Error::ParametersMismatch);
        }
        let mut z = alloc::vec![0; params.p.len()];
        let x = &self.x[self.x.len() - self.exponent_len..];
        if params.domain.exchange(x, &peer.y, &mut z) {
            Ok(z)
        } else {
            Err(Error::InvalidSharedSecret)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::{format, vec};
    fn composite_domain() -> Parameters {
        // Modulus 2^512-1, generator 2^128: g^4=1 and g^2!=1.
        // Deliberately composite to test degenerate shared-value rejection.
        let p = vec![0xff; 64];
        let mut g = vec![0; 17];
        g[0] = 1;
        Parameters::from_components(&p, &g, None).unwrap()
    }
    #[test]
    fn key_generation_from_a_fixed_tape_is_deterministic() {
        // The same tape gives the same key, as the fixed-tape benchmark
        // relies on.
        let params = composite_domain();
        let generate = || {
            let mut x = 0x9E37_79B9_7F4A_7C15u64;
            params
                .generate_private_key_with_rng(|buf: &mut [u8]| {
                    for b in buf {
                        x ^= x << 13;
                        x ^= x >> 7;
                        x ^= x << 17;
                        *b = x as u8;
                    }
                    Ok::<_, ()>(())
                })
                .unwrap()
        };
        let (a, b) = (generate(), generate());
        assert_eq!(a.private_component(), b.private_component());
        assert_eq!(a.public_key().component(), b.public_key().component());
    }
    #[test]
    fn generation_from_a_fixed_tape_is_deterministic() {
        // The same tape gives the same safe prime, as the fixed-tape
        // benchmark relies on.
        let generate = || {
            let mut x = 0x9E37_79B9_7F4A_7C15u64;
            Parameters::generate_with_rng(512, 2, |buf: &mut [u8]| {
                for b in buf {
                    x ^= x << 13;
                    x ^= x >> 7;
                    x ^= x << 17;
                    *b = x as u8;
                }
                Ok::<_, ()>(())
            })
            .unwrap()
        };
        let (a, b) = (generate(), generate());
        assert_eq!(a.components(), b.components());
        assert_eq!(a.key_size(), 512);
    }
    #[test]
    fn shared_failure_and_key_wiping() {
        let params = composite_domain();
        // y = g^2 = 2^256.
        let mut y = vec![0; 33];
        y[0] = 1;
        let k = PrivateKey::from_components(&params, &y, &[2]).unwrap();
        assert_eq!(k.exchange(k.public_key()), Err(Error::InvalidSharedSecret));
        let mut x = vec![2];
        let mut k = PrivateKey::from_components(&params, &y, &x).unwrap();
        x[0] = 0;
        assert_eq!(k.private_component()[63], 2);
        assert!(k.private_component()[..63].iter().all(|&b| b == 0));
        // Exercise the same wipe as Drop while the allocation is alive;
        // dropping then runs the verified wipe once more and frees it.
        zeroize(&mut k.x);
        assert!(k.x.iter().all(|&b| b == 0));
        drop(k);
        assert!(format!("{:?}", params.clone()).contains("Parameters"));
    }
    #[test]
    fn random_failures_and_degenerate_key_retry() {
        let params = composite_domain();
        assert_eq!(
            params.generate_with(|_| Err(())).unwrap_err(),
            Error::Randomness
        );
        assert_eq!(
            params
                .generate_with(|out| {
                    out.fill(0);
                    Ok::<_, ()>(())
                })
                .unwrap_err(),
            Error::TooManyIterations
        );
        // Scalars of 0 or at least p are out of range, and 4 gives the
        // degenerate g^4 = 1 (g has order 4 in this algebraic fixture).
        for last in [4, 255] {
            assert_eq!(
                params
                    .generate_with(|out| {
                        out.fill(if last == 255 { 255 } else { 0 });
                        *out.last_mut().unwrap() = last;
                        Ok::<_, ()>(())
                    })
                    .unwrap_err(),
                Error::TooManyIterations
            );
        }
        let mut attempts = 0;
        let key = params
            .generate_with(|out| {
                attempts += 1;
                out.fill(0);
                *out.last_mut().unwrap() = if attempts == 1 { 4 } else { 3 };
                Ok::<_, ()>(())
            })
            .unwrap();
        assert_eq!(attempts, 2);
        assert_eq!(key.private_component()[63], 3);
        // g^3 = 2^384.
        let y = key.public_key().component();
        assert_eq!(y[0], 1);
        assert!(y[1..].iter().all(|&b| b == 0));
    }
    #[test]
    fn key_search_consumes_rejected_attempts() {
        let params = composite_domain();
        let domain = &params.domain;
        // Scalars 0 (out of range), 4 (degenerate: g^4 = 1) and 3, one
        // attempt of 64 bytes each, in one tape.
        let mut tape = vec![0; 3 * 64];
        tape[63] = 0;
        tape[127] = 4;
        tape[191] = 3;
        let (mut x, mut y) = (vec![0xa5; 64], vec![0x5a; 64]);
        let mut state = domain.key_state();
        assert_eq!(&state[..4], &[128, 128, 64, 64]);
        // Only the budgets and width constrain a call. The incoming
        // request and private controller workspace may hold arbitrary
        // u64 words, including nonzero upper halves on a 32-bit target.
        state[3..].fill(u64::MAX);
        assert_eq!(
            domain.key_search(&mut state, &tape, &mut x, &mut y),
            (1, 192, 0)
        );
        assert_eq!(&state[..4], &[0, 0, 64, 0]);
        assert_eq!(x, tape[128..]);
        assert_eq!(y[15], 1);
        // A tape that ends inside the second attempt: the first is
        // consumed, and the controller asks for one attempt's bytes again,
        // with the scalar budget one smaller.
        let mut state = domain.key_state();
        state[3..].fill(u64::MAX);
        let (status, used, request) = domain.key_search(&mut state, &tape[..100], &mut x, &mut y);
        assert_eq!((status, used, request), (0, 64, 64));
        assert_eq!(&state[..4], &[128, 127, 64, 64]);
        assert!(x.iter().chain(&y).all(|&b| b == 0));
        // A degenerate value resets the scalar budget.
        let (status, used, _) = domain.key_search(&mut state, &tape[64..128], &mut x, &mut y);
        assert_eq!((status, used), (0, 64));
        assert_eq!(&state[..2], &[127, 128]);
        // Out-of-range scalars until the scalar budget runs out.
        let mut state = domain.key_state();
        state[1] = 2;
        let zeros = vec![0; 3 * 64];
        assert_eq!(
            domain.key_search(&mut state, &zeros, &mut x, &mut y),
            (3, 128, 0)
        );
        assert_eq!(&state[..4], &[0, 0, 64, 0]);
        assert!(x.iter().chain(&y).all(|&b| b == 0));
    }
    #[test]
    fn partial_limb_moduli_and_short_exponents() {
        // Algebraic regression fixtures, with no claim of primality:
        // p = leading * 256^(len-1) + 1, g = 2. With x = 3 and
        // peer exponent 7, the public values are 8 and 128 and the
        // shared value is 2^21, below each modulus. These widths cross
        // byte, native-word, and packed-u64 workspace boundaries.
        for len in [65, 71, 129, 1024] {
            for leading in [1, 128] {
                let mut p = vec![0; len];
                p[0] = leading;
                p[len - 1] = 1;
                let params = Parameters::from_components(&p, &[2], None).unwrap();
                let key = PrivateKey::from_components(&params, &[8], &[3]).unwrap();
                let peer = PublicKey::from_components(&params, &[128]).unwrap();
                let out = key.exchange(&peer).unwrap();
                assert!(out[..len - 3].iter().all(|&b| b == 0));
                assert_eq!(&out[len - 3..], &[32, 0, 0]);
                let generated = params
                    .generate_with(|out| {
                        out.fill(0);
                        *out.last_mut().unwrap() = 3;
                        Ok::<_, ()>(())
                    })
                    .unwrap();
                assert_eq!(
                    generated.public_key().component(),
                    key.public_key().component()
                );
            }
        }
    }
}
