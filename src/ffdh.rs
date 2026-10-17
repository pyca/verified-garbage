//! Finite-field Diffie–Hellman, for the component API used by cryptography.
//!
//! Public-key validation and exchange call the verified FFDH operations.
//! Exchange secret exponentiation follows a fixed schedule over the public encoding
//! length supplied at import, or the public sampling bound for generated keys.
//! All domain arithmetic and secret exponentiation run in verified code.
//! Private-key generation samples and validates the scalar in verified code.
//! Rust obtains random bytes, retries rejected attempts and packs inputs and
//! results. On x86-64, parameter generation runs entirely in verified code,
//! including its attempt limit and entropy requests; Rust allocates and
//! fills the random tape it asks for. On AArch64, Rust still runs the search
//! with the shared verified Miller–Rabin round, preparing its workspace and
//! selecting independent witnesses.
//! Imported parameters receive structural and algebraic checks; callers must
//! establish primality/provenance. Optional q enables subgroup checks.
//! Exchange returns exactly ceil(bits(p)/8) bytes, without applying a KDF.

#![cfg(all(
    any(target_arch = "x86_64", target_arch = "aarch64"),
    feature = "alloc"
))]

mod arithmetic;
mod domain;
mod generation;

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

    /// Borrow canonical unsigned big-endian (p,g,q), preserving q's presence.
    pub fn components(&self) -> (&[u8], &[u8], Option<&[u8]>) {
        (&self.p, &self.g, self.q.as_deref())
    }

    /// The bit length of p.
    pub fn key_size(&self) -> usize {
        arithmetic::bits(&self.p)
    }

    /// Generate a private key with a uniform scalar in 1..q or 1..p-1
    /// when q is absent. Reject degenerate public keys and retry.
    pub fn generate_private_key(&self) -> Result<PrivateKey, Error> {
        self.generate_with(getrandom::fill)
    }

    /// Verified code draws and checks the scalar and its public value.
    /// Retry up to 128 times for an in-range scalar and up to 128 times
    /// for a public value that is not degenerate.
    fn generate_with<E>(
        &self,
        mut fill: impl FnMut(&mut [u8]) -> Result<(), E>,
    ) -> Result<PrivateKey, Error> {
        let len = self.p.len();
        let exponent_len = self.q.as_ref().map_or(len, Vec::len);
        let mut rand = alloc::vec![0; len];
        let mut x = alloc::vec![0; len];
        let mut y = alloc::vec![0; len];
        let mut result = Err(Error::TooManyIterations);
        'keys: for _ in 0..128 {
            for _ in 0..128 {
                if fill(&mut rand).is_err() {
                    result = Err(Error::Randomness);
                    break 'keys;
                }
                match self.domain.generate_key(&rand, &mut x, &mut y) {
                    1 => {
                        result = Ok(PrivateKey {
                            public: PublicKey {
                                params: self.clone(),
                                y: canonical(&y).to_vec(),
                            },
                            x: core::mem::take(&mut x),
                            exponent_len,
                        });
                        break 'keys;
                    }
                    2 => continue,
                    _ => continue 'keys,
                }
            }
            break;
        }
        // The last candidate scalar, if no attempt succeeded.
        zeroize(&mut x);
        zeroize(&mut rand);
        result
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
        Ok(Self {
            public: PublicKey {
                params: params.clone(),
                y: y.to_vec(),
            },
            x: scalar(x, params.p.len()),
            exponent_len,
        })
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
        assert_eq!(
            params
                .generate_with(|out| {
                    out.fill(0);
                    *out.last_mut().unwrap() = 4;
                    Ok::<_, ()>(())
                })
                .unwrap_err(),
            Error::TooManyIterations
        );
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
    }
    #[test]
    fn generated_attempt_masks_failed_outputs() {
        let params = composite_domain();
        // In this algebraic fixture g has order 4. Scalars 0 and p are
        // outside the range; 4 produces 1; 3 produces g^3 = 2^384.
        for (scalar, status) in [(0, 2), (4, 3), (3, 1), (255, 2)] {
            let mut rand = vec![0; 64];
            if scalar == 255 {
                rand.fill(255);
            } else {
                rand[63] = scalar;
            }
            let mut x = vec![0xa5; 64];
            let mut y = vec![0x5a; 64];
            assert_eq!(params.domain.generate_key(&rand, &mut x, &mut y), status);
            if status == 1 {
                assert_eq!(x, rand);
                assert_eq!(y[15], 1);
                assert!(y[..15].iter().chain(&y[16..]).all(|&b| b == 0));
            } else {
                assert!(x.iter().chain(&y).all(|&b| b == 0));
            }
        }
    }
}
