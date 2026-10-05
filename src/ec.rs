//! The elliptic curves of [`ecdsa`](crate::ecdsa) and [`ecdh`](crate::ecdh):
//! the encodings of their keys and signatures.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

mod sealed {
    pub trait Sealed {}
}

/// A curve that ECDSA signs over and ECDH exchanges keys on.
pub trait Curve: sealed::Sealed {
    /// The encoding of a private key: the integer `d` in `[1, n − 1]`, most
    /// significant byte first (`[u8; 32]` for P-256, `[u8; 48]` for P-384,
    /// `[u8; 66]` for P-521).
    type PrivateKey: AsMut<[u8]> + Clone;
    /// The encoding of a public key: the uncompressed form of SEC 1 §2.3.3,
    /// `04 ‖ x ‖ y`, each coordinate most significant byte first
    /// (`[u8; 65]` for P-256, `[u8; 97]` for P-384, `[u8; 133]` for P-521).
    type PublicKey: Clone + core::fmt::Debug + PartialEq + Eq;
    /// The encoding of a signature: `r ‖ s`, each most significant byte
    /// first (`[u8; 64]` for P-256, `[u8; 96]` for P-384, `[u8; 132]` for
    /// P-521).
    type Signature;
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
#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum P521 {}

#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
impl sealed::Sealed for P521 {}

#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
impl Curve for P521 {
    type PrivateKey = [u8; 66];
    type PublicKey = [u8; 133];
    type Signature = [u8; 132];
}
