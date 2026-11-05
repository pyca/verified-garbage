//! Elliptic curves for [`ecdsa`](crate::ecdsa) and [`ecdh`](crate::ecdh):
//! [`P192`], [`P224`], [`P256`], [`P384`], [`P521`], [`Secp256k1`],
//! [`BrainpoolP256r1`], [`BrainpoolP384r1`] and [`BrainpoolP512r1`] (each a
//! [`Curve`]), and their public keys ([`PublicKey<C>`]).
//!
//! Each curve converts a SEC 1 public key between its compressed and
//! uncompressed forms, validating it (`compress_public_key`,
//! `decompress_public_key`), and on x86-64 validates one on its own
//! (`validate_public_key`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

pub(crate) mod brainpoolp256r1;
pub(crate) mod brainpoolp384r1;
pub(crate) mod brainpoolp512r1;
mod compressed;
mod p192;
pub(crate) mod p224;
pub(crate) mod p256;
pub(crate) mod p384;
pub(crate) mod p521;
pub(crate) mod secp256k1;
mod validate;

pub(crate) mod sealed {
    use super::Curve;

    /// A curve's public keys (`vg_ec_<curve>_public_key`), implemented in
    /// its file here.
    pub trait Sealed {
        /// The public key `Q = dG` of `d`, or `None` if `d` is not in
        /// `[1, n − 1]`.
        fn public_key(d: &<Self as Curve>::PrivateKey) -> Option<<Self as Curve>::PublicKey>
        where
            Self: Curve;
    }

    /// ECDH on a curve (`vg_ecdh_<curve>`), implemented in its file in
    /// [`ecdh`](crate::ecdh).
    pub trait Exchange {
        /// The x-coordinate of `dQ`, or `None` if `d` is not in `[1, n − 1]`
        /// or `q` is not a valid public key.
        fn exchange(
            d: &<Self as Curve>::PrivateKey,
            q: &<Self as Curve>::PublicKey,
        ) -> Option<<Self as Curve>::SharedSecret>
        where
            Self: Curve;
    }
}

/// A curve that ECDSA signs over and ECDH exchanges keys on, and the
/// encodings of its keys, shared secrets and signatures, each an array of
/// bytes.
pub trait Curve: sealed::Sealed + sealed::Exchange {
    /// The encoding of a private key: the integer `d` in `[1, n − 1]`, most
    /// significant byte first (`[u8; 28]` for P-224, `[u8; 32]` for P-256,
    /// `[u8; 48]` for P-384, `[u8; 66]` for P-521).
    type PrivateKey: AsMut<[u8]> + Clone;
    /// The encoding of a public key: the uncompressed form of SEC 1 §2.3.3,
    /// `04 ‖ x ‖ y`, each coordinate most significant byte first
    /// (`[u8; 57]` for P-224, `[u8; 65]` for P-256, `[u8; 97]` for P-384,
    /// `[u8; 133]` for P-521).
    type PublicKey: Clone + core::fmt::Debug + PartialEq + Eq;
    /// The encoding of an ECDH shared secret: an x-coordinate, most
    /// significant byte first (`[u8; 28]` for P-224, `[u8; 32]` for P-256,
    /// `[u8; 48]` for P-384, `[u8; 66]` for P-521).
    type SharedSecret;
    /// The encoding of a signature: `r ‖ s`, each most significant byte
    /// first (`[u8; 56]` for P-224, `[u8; 64]` for P-256, `[u8; 96]` for
    /// P-384, `[u8; 132]` for P-521).
    type Signature;
}

/// A public key on the curve `C`.
///
/// Importing one does not check it: an ECDH exchange or an ECDSA
/// verification with it checks that it is valid (SP 800-56A §5.6.2.3.3), in
/// the same call of verified code, and fails if it is not.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicKey<C: Curve> {
    pub(crate) q: C::PublicKey,
}

impl<C: Curve> PublicKey<C> {
    /// Imports a public key, in the uncompressed form of SEC 1 §2.3.3.
    pub fn from_bytes(q: &C::PublicKey) -> Self {
        Self { q: q.clone() }
    }

    /// The public key, as [`from_bytes`](Self::from_bytes) takes it.
    pub fn as_bytes(&self) -> &C::PublicKey {
        &self.q
    }

    /// The public key `Q = dG` of the private key `d`, or `None` if `d` is
    /// not in `[1, n − 1]`.
    pub(crate) fn derive(d: &C::PrivateKey) -> Option<Self> {
        C::public_key(d).map(|q| Self { q })
    }
}

/// The curve P-224 (FIPS 186-5's secp224r1; SP 800-186 §3.2.1.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum P224 {}

impl sealed::Sealed for P224 {
    fn public_key(d: &[u8; 28]) -> Option<[u8; 57]> {
        p224::public_key(d)
    }
}

impl Curve for P224 {
    type PrivateKey = [u8; 28];
    type PublicKey = [u8; 57];
    type SharedSecret = [u8; 28];
    type Signature = [u8; 56];
}

/// The curve P-256 (FIPS 186-5's secp256r1; SP 800-186 §3.2.1.3).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum P256 {}

impl sealed::Sealed for P256 {
    fn public_key(d: &[u8; 32]) -> Option<[u8; 65]> {
        p256::public_key(d)
    }
}

impl Curve for P256 {
    type PrivateKey = [u8; 32];
    type PublicKey = [u8; 65];
    type SharedSecret = [u8; 32];
    type Signature = [u8; 64];
}

/// The curve P-384 (FIPS 186-5's secp384r1; SP 800-186 §3.2.1.4).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum P384 {}

impl sealed::Sealed for P384 {
    fn public_key(d: &[u8; 48]) -> Option<[u8; 97]> {
        p384::public_key(d)
    }
}

impl Curve for P384 {
    type PrivateKey = [u8; 48];
    type PublicKey = [u8; 97];
    type SharedSecret = [u8; 48];
    type Signature = [u8; 96];
}

/// The curve P-521 (FIPS 186-5's secp521r1; SP 800-186 §3.2.1.5).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum P521 {}

impl sealed::Sealed for P521 {
    fn public_key(d: &[u8; 66]) -> Option<[u8; 133]> {
        p521::public_key(d)
    }
}

impl Curve for P521 {
    type PrivateKey = [u8; 66];
    type PublicKey = [u8; 133];
    type SharedSecret = [u8; 66];
    type Signature = [u8; 132];
}

/// The curve secp256k1 (SEC 2 version 2.0, §2.4.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Secp256k1 {}

impl sealed::Sealed for Secp256k1 {
    fn public_key(d: &[u8; 32]) -> Option<[u8; 65]> {
        secp256k1::public_key(d)
    }
}

impl Curve for Secp256k1 {
    type PrivateKey = [u8; 32];
    type PublicKey = [u8; 65];
    type SharedSecret = [u8; 32];
    type Signature = [u8; 64];
}

/// The curve brainpoolP256r1 (RFC 5639 §3.4).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BrainpoolP256r1 {}

impl sealed::Sealed for BrainpoolP256r1 {
    fn public_key(d: &[u8; 32]) -> Option<[u8; 65]> {
        brainpoolp256r1::public_key(d)
    }
}

impl Curve for BrainpoolP256r1 {
    type PrivateKey = [u8; 32];
    type PublicKey = [u8; 65];
    type SharedSecret = [u8; 32];
    type Signature = [u8; 64];
}

/// The curve brainpoolP384r1 (RFC 5639 §3.6).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BrainpoolP384r1 {}

impl sealed::Sealed for BrainpoolP384r1 {
    fn public_key(d: &[u8; 48]) -> Option<[u8; 97]> {
        brainpoolp384r1::public_key(d)
    }
}

impl Curve for BrainpoolP384r1 {
    type PrivateKey = [u8; 48];
    type PublicKey = [u8; 97];
    type SharedSecret = [u8; 48];
    type Signature = [u8; 96];
}

/// The curve brainpoolP512r1 (RFC 5639 §3.7).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BrainpoolP512r1 {}

impl sealed::Sealed for BrainpoolP512r1 {
    fn public_key(d: &[u8; 64]) -> Option<[u8; 129]> {
        brainpoolp512r1::public_key(d)
    }
}

impl Curve for BrainpoolP512r1 {
    type PrivateKey = [u8; 64];
    type PublicKey = [u8; 129];
    type SharedSecret = [u8; 64];
    type Signature = [u8; 128];
}

/// The curve P-192 (NIST SP 800-186, §3.2.1.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum P192 {}

impl sealed::Sealed for P192 {
    fn public_key(d: &[u8; 24]) -> Option<[u8; 49]> {
        p192::public_key(d)
    }
}

impl Curve for P192 {
    type PrivateKey = [u8; 24];
    type PublicKey = [u8; 49];
    type SharedSecret = [u8; 24];
    type Signature = [u8; 48];
}
