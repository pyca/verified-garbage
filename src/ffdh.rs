//! Finite-field Diffie–Hellman, for the component API used by cryptography.
//!
//! Secret exponentiation follows a fixed schedule over the public encoding
//! length supplied at import, or the public sampling bound for generated keys.
//! Every multiplication calls the verified Montgomery primitive
//! (`VG.Spec.Rsa.Mont.mulContract`); every selection calls the verified
//! `VG.Spec.Ffdh.chooseContract`. Rust composes these primitives, validates
//! domains and keys, samples randomness and encodes the result. These Rust
//! operations, as elsewhere in the crate, are outside the Lean proof boundary.
//! Imported parameters receive structural and algebraic checks; callers must
//! establish primality/provenance. Optional q enables subgroup checks.
//! Exchange returns exactly ceil(bits(p)/8) bytes, without applying a KDF.

#![cfg(all(
    any(target_arch = "x86_64", target_arch = "aarch64"),
    feature = "alloc"
))]

mod arithmetic;
mod generation;

use crate::zeroize::zeroize;
use alloc::vec::Vec;
use arithmetic::{Montgomery, canonical, minus_one, scalar, value_cmp};
use core::fmt;

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

/// Imported domain components and their public Montgomery precomputation.
#[derive(Clone, Debug)]
pub struct Parameters {
    p: Vec<u8>,
    g: Vec<u8>,
    q: Option<Vec<u8>>,
    mont: Montgomery,
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
        let p = canonical(p);
        let g = canonical(g);
        let bits = arithmetic::bits(p);
        if !(MIN_BITS..=MAX_BITS).contains(&bits) || p[p.len() - 1] & 1 == 0 {
            return Err(Error::InvalidParameters);
        }
        let p1 = minus_one(p);
        if value_cmp(g, &[1]).is_le() || value_cmp(g, &p1).is_ge() {
            return Err(Error::InvalidParameters);
        }
        let mont = Montgomery::new(p);
        let q = q.map(canonical);
        if let Some(q) = q
            && (value_cmp(q, &[2]).is_le()
                || q[q.len() - 1] & 1 == 0
                || value_cmp(q, &p1).is_ge()
                || !arithmetic::divides(q, &p1)
                || value_cmp(&mont.power(g, q), &[1]).is_ne())
        {
            return Err(Error::InvalidParameters);
        }
        Ok(Self {
            p: p.to_vec(),
            g: g.to_vec(),
            q: q.map(<[u8]>::to_vec),
            mont,
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

    fn generate_with<E>(
        &self,
        mut fill: impl FnMut(&mut [u8]) -> Result<(), E>,
    ) -> Result<PrivateKey, Error> {
        let upper = self.q.clone().unwrap_or_else(|| minus_one(&self.p));
        for _ in 0..128 {
            let mut x = generation::sample(&upper, &mut fill)?;
            let mut padded = alloc::vec![0; self.p.len()];
            let offset = padded.len() - x.len();
            padded[offset..].copy_from_slice(&x);
            let result = PrivateKey::from_padded(self, padded, upper.len());
            zeroize(&mut x);
            match result {
                Err(Error::InvalidKey) => continue,
                r => return r,
            }
        }
        Err(Error::TooManyIterations)
    }

    fn public_valid(&self, y: &[u8]) -> bool {
        value_cmp(y, &[1]).is_gt()
            && value_cmp(y, &minus_one(&self.p)).is_lt()
            && self
                .q
                .as_ref()
                .is_none_or(|q| value_cmp(&self.mont.power(y, q), &[1]).is_eq())
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
        if !params.public_valid(y) {
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
        let key = Self::from_private_component(params, x)?;
        if !crate::ct::eq(&key.public.y, canonical(y)) {
            return Err(Error::InvalidKey);
        }
        Ok(key)
    }
    /// Import x and derive y. x is unsigned big-endian; its encoding length
    /// is public and determines the exponentiation schedule. Import validation
    /// may reveal whether x is in range, and is not a constant-time parser.
    fn from_private_component(params: &Parameters, x: &[u8]) -> Result<Self, Error> {
        let upper = params.q.clone().unwrap_or_else(|| minus_one(&params.p));
        if value_cmp(x, &[0]).is_le() || value_cmp(x, &upper).is_ge() {
            return Err(Error::InvalidKey);
        }
        let exponent_len = x.len().min(params.p.len());
        let x = scalar(x, params.p.len());
        Self::from_padded(params, x, exponent_len)
    }
    fn from_padded(params: &Parameters, x: Vec<u8>, exponent_len: usize) -> Result<Self, Error> {
        let y = params.mont.power(&params.g, &x[x.len() - exponent_len..]);
        if !params.public_valid(&y) {
            let mut x = x;
            zeroize(&mut x);
            return Err(Error::InvalidKey);
        }
        Ok(Self {
            public: PublicKey {
                params: params.clone(),
                y: canonical(&y).to_vec(),
            },
            x,
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
        let mut z = params
            .mont
            .power(&peer.y, &self.x[self.x.len() - self.exponent_len..]);
        let one = scalar(&[1], params.p.len());
        let zero = scalar(&[0], params.p.len());
        let p1 = minus_one(&params.p);
        let invalid = crate::ct::eq(&z, &one) | crate::ct::eq(&z, &zero) | crate::ct::eq(&z, &p1);
        if invalid {
            zeroize(&mut z);
            return Err(Error::InvalidSharedSecret);
        }
        Ok(z)
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
        let k = PrivateKey::from_private_component(&params, &[2]).unwrap();
        assert_eq!(k.exchange(k.public_key()), Err(Error::InvalidSharedSecret));
        let mut x = vec![2];
        let k = PrivateKey::from_private_component(&params, &x).unwrap();
        x[0] = 0;
        assert_eq!(k.private_component()[63], 2);
        assert!(k.private_component()[..63].iter().all(|&b| b == 0));
        let mut k = core::mem::ManuallyDrop::new(k);
        // Keep the allocation alive while exercising the same wipe as Drop;
        // then dropping runs the verified wipe once more and frees it.
        zeroize(&mut k.x);
        assert!(k.x.iter().all(|&b| b == 0));
        unsafe {
            core::mem::ManuallyDrop::drop(&mut k);
        }
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
    fn selection_is_by_low_bit() {
        for a in [0, 1, u64::MAX, 0x123456789abcdef0] {
            for b in [0, 1, u64::MAX, 0xfedcba9876543210] {
                for bit in [0, 1, 2, 3, u64::MAX] {
                    // SAFETY: no preconditions.
                    assert_eq!(
                        unsafe { crate::arch::ffdh::vg_ffdh_choose(a, b, bit) },
                        if bit & 1 == 0 { a } else { b }
                    );
                }
            }
        }
    }
}
