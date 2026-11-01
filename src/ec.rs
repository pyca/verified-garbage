//! The elliptic curves of [`ecdsa`](crate::ecdsa) and [`ecdh`](crate::ecdh):
//! the encodings of their keys and signatures.
//!
//! Each curve exposes `compress_public_key` and `decompress_public_key` (on
//! RISC-V, P-256 alone), and on x86-64 `validate_public_key`: each validates
//! the SEC 1 point in one call of a verified function.

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
pub(crate) mod p224;
pub(crate) mod p256;
pub(crate) mod p384;
pub(crate) mod p521;
pub(crate) mod secp256k1;
mod validate;

mod sealed {
    pub trait Sealed {}
}

/// A curve that ECDSA signs over and ECDH exchanges keys on.
pub trait Curve: sealed::Sealed {
    /// The encoding of a private key: the integer `d` in `[1, n − 1]`, most
    /// significant byte first (`[u8; 28]` for P-224, `[u8; 32]` for P-256,
    /// `[u8; 48]` for P-384, `[u8; 66]` for P-521).
    type PrivateKey: AsMut<[u8]> + Clone;
    /// The encoding of a public key: the uncompressed form of SEC 1 §2.3.3,
    /// `04 ‖ x ‖ y`, each coordinate most significant byte first
    /// (`[u8; 57]` for P-224, `[u8; 65]` for P-256, `[u8; 97]` for P-384,
    /// `[u8; 133]` for P-521).
    type PublicKey: Clone + core::fmt::Debug + PartialEq + Eq;
    /// The encoding of a signature: `r ‖ s`, each most significant byte
    /// first (`[u8; 56]` for P-224, `[u8; 64]` for P-256, `[u8; 96]` for
    /// P-384, `[u8; 132]` for P-521).
    type Signature;
}

/// The curve P-224 (FIPS 186-5's secp224r1; SP 800-186 §3.2.1.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum P224 {}

impl sealed::Sealed for P224 {}

impl Curve for P224 {
    type PrivateKey = [u8; 28];
    type PublicKey = [u8; 57];
    type Signature = [u8; 56];
}

/// The curve P-256 (FIPS 186-5's secp256r1; SP 800-186 §3.2.1.3).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum P256 {}

impl sealed::Sealed for P256 {}

impl Curve for P256 {
    type PrivateKey = [u8; 32];
    type PublicKey = [u8; 65];
    type Signature = [u8; 64];
}

/// The curve P-384 (FIPS 186-5's secp384r1; SP 800-186 §3.2.1.4).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum P384 {}

impl sealed::Sealed for P384 {}

impl Curve for P384 {
    type PrivateKey = [u8; 48];
    type PublicKey = [u8; 97];
    type Signature = [u8; 96];
}

/// The curve P-521 (FIPS 186-5's secp521r1; SP 800-186 §3.2.1.5).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum P521 {}

impl sealed::Sealed for P521 {}

impl Curve for P521 {
    type PrivateKey = [u8; 66];
    type PublicKey = [u8; 133];
    type Signature = [u8; 132];
}

/// The curve secp256k1 (SEC 2 version 2.0, §2.4.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Secp256k1 {}

impl sealed::Sealed for Secp256k1 {}

impl Curve for Secp256k1 {
    type PrivateKey = [u8; 32];
    type PublicKey = [u8; 65];
    type Signature = [u8; 64];
}

/// The curve brainpoolP256r1 (RFC 5639 §3.4).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BrainpoolP256r1 {}

impl sealed::Sealed for BrainpoolP256r1 {}

impl Curve for BrainpoolP256r1 {
    type PrivateKey = [u8; 32];
    type PublicKey = [u8; 65];
    type Signature = [u8; 64];
}

/// The curve brainpoolP384r1 (RFC 5639 §3.6).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BrainpoolP384r1 {}

impl sealed::Sealed for BrainpoolP384r1 {}

impl Curve for BrainpoolP384r1 {
    type PrivateKey = [u8; 48];
    type PublicKey = [u8; 97];
    type Signature = [u8; 96];
}

/// The curve brainpoolP512r1 (RFC 5639 §3.7).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BrainpoolP512r1 {}

impl sealed::Sealed for BrainpoolP512r1 {}

impl Curve for BrainpoolP512r1 {
    type PrivateKey = [u8; 64];
    type PublicKey = [u8; 129];
    type Signature = [u8; 128];
}

/// The curve P-192 (NIST SP 800-186, §3.2.1.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum P192 {}

impl sealed::Sealed for P192 {}

impl Curve for P192 {
    type PrivateKey = [u8; 24];
    type PublicKey = [u8; 49];
    type Signature = [u8; 48];
}
