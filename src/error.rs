//! The errors the modules share.
//!
//! A function returns the type that names the failures it can have; a module
//! whose failures no other module shares has an `Error` of its own. The
//! messages do not name the algorithm: the caller knows which call failed.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

/// The key does not have a length the algorithm accepts. The constructor
/// (or one-shot function) that returns it says which lengths it accepts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InvalidKeyLength;

/// An input that a block mode takes in whole blocks of its block cipher is
/// not a whole number of blocks. The function that returns it says which
/// input: every call's for CBC and ECB, that of a call that does not end the
/// message for CFB, OFB and CTR, and the whole message's for the modes that
/// buffer a partial block (Blowfish-ECB's and RC2-CBC's `finalize`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IncompleteBlock;

/// The output buffer of an update is shorter than the bytes it would write
/// (which the type's `output_len` gives).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OutputTooSmall;

/// The MAC did not match: the message or the key is not what was
/// authenticated. HMAC, CMAC, Poly1305 and keyed BLAKE2 return it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InvalidMac;

/// Why an X25519 or X448 operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum XdhError {
    /// The shared secret is all zero: the peer's public key is a point of
    /// small order (RFC 7748 §6.1 for X25519, §6.2 for X448).
    ZeroSharedSecret,
    /// The operating system's random number generator failed.
    Randomness,
}

/// Why an ML-KEM-768 or ML-KEM-1024 operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MlKemError {
    /// A `SampleNTT` reached the bound on its loop's iterations (FIPS 203
    /// Appendix B), which happens with probability less than 2⁻²⁶¹ for each
    /// call: less than 2⁻²⁵⁸ in an ML-KEM-768 operation (9 calls) and 2⁻²⁵⁷
    /// in an ML-KEM-1024 one (16 calls).
    SampleBound,
    /// The encapsulation key failed the check of FIPS 203 §7.2.
    InvalidKey,
    /// The operating system's random number generator failed.
    Randomness,
}

/// Why an ML-DSA-44, ML-DSA-65 or ML-DSA-87 operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MlDsaError {
    /// A loop reached its bound (FIPS 204 Appendix C), which happens with
    /// probability about 2⁻²⁵⁶ or less.
    LoopBound,
    /// The context string is longer than 255 bytes (FIPS 204 Algorithms 2
    /// and 3).
    ContextTooLong,
    /// The signature is not valid.
    InvalidSignature,
    /// The operating system's random number generator failed.
    Randomness,
}

/// Why scrypt or Argon2 refused to derive a key, or to accept one.
#[cfg(feature = "alloc")]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PasswordHashError {
    /// The parameters (costs or lengths) are not valid: the function that
    /// returns it says which are.
    InvalidParameters,
    /// The memory the derivation needs, which the function that returns it
    /// gives, exceeds `max_memory` (or the address space).
    MemoryLimitExceeded,
    /// Allocating that memory failed.
    AllocationFailed,
    /// A `verify` derived a key other than the expected one: the password
    /// (or another input or a parameter) is not the one it was derived from.
    KeyMismatch,
}

/// Implements `core::fmt::Display` for each error struct `$ty`, writing
/// `$msg`, and `core::error::Error`.
macro_rules! impl_unit_error {
    ($($ty:ident => $msg:expr,)+) => {
        $(
            impl core::fmt::Display for $ty {
                fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                    f.write_str($msg)
                }
            }

            impl core::error::Error for $ty {}
        )+
    };
}

impl_unit_error! {
    InvalidKeyLength => "invalid key length",
    IncompleteBlock => "input is not a whole number of blocks",
    OutputTooSmall => "output buffer is too small",
    InvalidMac => "MAC does not match",
}

/// Implements `core::fmt::Display` for the error enum `$ty`, writing `$msg`
/// for `$variant`, and `core::error::Error`.
macro_rules! impl_error {
    ($ty:ident { $($variant:ident => $msg:expr,)+ }) => {
        impl core::fmt::Display for $ty {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.write_str(match self {
                    $(Self::$variant => $msg,)+
                })
            }
        }

        impl core::error::Error for $ty {}
    };
}
pub(crate) use impl_error;

impl_error! {
    XdhError {
        ZeroSharedSecret => "shared secret is all zero",
        Randomness => "random number generator failed",
    }
}

impl_error! {
    MlKemError {
        SampleBound => "ML-KEM sampling loop reached its bound",
        InvalidKey => "invalid ML-KEM encapsulation key",
        Randomness => "random number generator failed",
    }
}

impl_error! {
    MlDsaError {
        LoopBound => "ML-DSA loop reached its bound",
        ContextTooLong => "context is longer than 255 bytes",
        InvalidSignature => "invalid ML-DSA signature",
        Randomness => "random number generator failed",
    }
}

#[cfg(feature = "alloc")]
impl_error! {
    PasswordHashError {
        InvalidParameters => "invalid password hashing parameters",
        MemoryLimitExceeded => "derivation would need more than the memory limit",
        AllocationFailed => "could not allocate the derivation's memory",
        KeyMismatch => "derived key does not match",
    }
}

#[cfg(test)]
mod tests {
    extern crate std;

    use std::string::ToString;

    macro_rules! check {
        ($($e:expr),+ $(,)?) => {
            $(assert!(!$e.to_string().is_empty(), "{:?}", $e);)+
        };
    }

    /// Every value of the shared errors, and of the modules' own, has a
    /// message.
    #[test]
    fn errors_display() {
        check!(
            super::IncompleteBlock,
            super::InvalidKeyLength,
            super::InvalidMac,
            super::MlDsaError::ContextTooLong,
            super::MlDsaError::InvalidSignature,
            super::MlDsaError::LoopBound,
            super::MlDsaError::Randomness,
            super::MlKemError::InvalidKey,
            super::MlKemError::Randomness,
            super::MlKemError::SampleBound,
            super::OutputTooSmall,
            super::XdhError::Randomness,
            super::XdhError::ZeroSharedSecret,
            crate::aead::aes_ccm::Error::InvalidNonceLength,
            crate::aead::aes_ccm::Error::InvalidTextLength,
            crate::aead::aes_ccm::Error::TagMismatch,
            crate::aead::aes_gcm::Error::AadAfterText,
            crate::aead::aes_gcm::Error::InvalidAadLength,
            crate::aead::aes_gcm::Error::InvalidNonceLength,
            crate::aead::aes_gcm::Error::InvalidOutputLength,
            crate::aead::aes_gcm::Error::InvalidTextLength,
            crate::aead::aes_gcm::Error::TagMismatch,
            crate::aead::aes_gcm::Error::TooManyPieces,
            crate::aead::aes_gcm_siv::Error::InvalidAadLength,
            crate::aead::aes_gcm_siv::Error::InvalidTextLength,
            crate::aead::aes_gcm_siv::Error::TagMismatch,
            crate::aead::aes_ocb::Error::InvalidNonceLength,
            crate::aead::aes_ocb::Error::TagMismatch,
            crate::aead::aes_siv::Error::TagMismatch,
            crate::aead::aes_siv::Error::TooManyComponents,
            crate::cipher::aes::XtsError::DataUnitTooLong,
            crate::cipher::aes::XtsError::DataUnitTooShort,
            crate::cipher::aes::XtsError::EqualKeyHalves,
            crate::cipher::aes::XtsError::InvalidKeyLength,
            crate::cipher::aes::XtsError::InvalidOutputLength,
            crate::ec::Error::InvalidKey,
            crate::ec::Error::InvalidSignature,
            crate::aead::chacha20poly1305::Error::InvalidOutputLength,
            crate::aead::chacha20poly1305::Error::InvalidTextLength,
            crate::aead::chacha20poly1305::Error::TagMismatch,
            crate::aead::chacha20poly1305::Error::TooManyPieces,
            crate::ed25519::Error::InvalidSignature,
            crate::ed448::Error::ContextTooLong,
            crate::ed448::Error::InvalidSignature,
            crate::cipher::rc2::Error::InvalidEffectiveBits,
            crate::cipher::rc2::Error::InvalidIvLength,
            crate::cipher::rc2::Error::InvalidKeyLength,
            crate::aead::sm4_gcm::Error::AadAfterText,
            crate::aead::sm4_gcm::Error::InvalidAadLength,
            crate::aead::sm4_gcm::Error::InvalidNonceLength,
            crate::aead::sm4_gcm::Error::InvalidTextLength,
            crate::aead::sm4_gcm::Error::TagMismatch,
        );
        #[cfg(feature = "alloc")]
        check!(
            super::PasswordHashError::AllocationFailed,
            super::PasswordHashError::InvalidParameters,
            super::PasswordHashError::KeyMismatch,
            super::PasswordHashError::MemoryLimitExceeded,
        );
    }
}
