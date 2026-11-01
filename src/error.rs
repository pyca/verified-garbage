//! What the modules' errors share: the one `InvalidKeyLength`, which each
//! module whose constructor can fail only on the key's length re-exports,
//! and `impl_error!`, which implements `Display` and `core::error::Error`
//! for an error enum.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

// Each module's re-export has a doc of the key lengths it accepts, which
// rustdoc puts before this one: the blank first line makes this a paragraph
// of its own.
///
/// Every module whose constructor fails only on the length of the key
/// returns this one type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InvalidKeyLength;

impl core::fmt::Display for InvalidKeyLength {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("invalid key length")
    }
}

impl core::error::Error for InvalidKeyLength {}

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

#[cfg(test)]
mod tests {
    extern crate std;

    use std::string::ToString;

    macro_rules! check {
        ($($e:expr),+ $(,)?) => {
            $(assert!(!$e.to_string().is_empty(), "{:?}", $e);)+
        };
    }

    /// Every error value of every module RISC-V has so far has a message.
    #[cfg(target_arch = "riscv64")]
    #[test]
    fn errors_display() {
        check!(
            super::InvalidKeyLength,
            crate::aes_cbc::Error::IncompleteBlock,
            crate::aes_cbc::Error::InvalidKeyLength,
            crate::aes_ccm::Error::InvalidKeyLength,
            crate::aes_ccm::Error::InvalidNonceLength,
            crate::aes_ccm::Error::InvalidTextLength,
            crate::aes_ccm::Error::TagMismatch,
            crate::aes_ecb::Error::IncompleteBlock,
            crate::aes_ecb::Error::InvalidKeyLength,
            crate::blowfish_cbc::Error::IncompleteBlock,
            crate::blowfish_cbc::Error::InvalidKeyLength,
            crate::blowfish_ecb::Error::IncompleteBlock,
            crate::blowfish_ecb::Error::InvalidKeyLength,
            crate::blowfish_ecb::Error::OutputTooSmall,
            crate::camellia_cbc::Error::IncompleteBlock,
            crate::camellia_cbc::Error::InvalidKeyLength,
            crate::camellia_ecb::Error::IncompleteBlock,
            crate::camellia_ecb::Error::InvalidKeyLength,
            crate::idea_cbc::Error::IncompleteBlock,
            crate::idea_cbc::Error::InvalidKeyLength,
            crate::idea_ecb::Error::IncompleteBlock,
            crate::idea_ecb::Error::InvalidKeyLength,
            crate::rc2_cbc::Error::IncompleteBlock,
            crate::rc2_cbc::Error::InvalidEffectiveBits,
            crate::rc2_cbc::Error::InvalidIvLength,
            crate::rc2_cbc::Error::InvalidKeyLength,
            crate::rc2_cbc::Error::OutputTooSmall,
            crate::rc4::Error::InvalidKeyLength,
            crate::seed_cbc::Error::IncompleteBlock,
            crate::seed_cbc::Error::InvalidKeyLength,
            crate::seed_ecb::Error::IncompleteBlock,
            crate::sm4_cbc::Error::IncompleteBlock,
            crate::sm4_ecb::Error::IncompleteBlock,
            crate::triple_des_cbc::Error::IncompleteBlock,
            crate::triple_des_cbc::Error::InvalidKeyLength,
            crate::triple_des_ecb::Error::IncompleteBlock,
            crate::triple_des_ecb::Error::InvalidKeyLength,
            crate::x25519::Error::Randomness,
            crate::x25519::Error::ZeroSharedSecret,
        );
    }

    /// Every error value of every module has a message.
    #[cfg(not(target_arch = "riscv64"))]
    #[test]
    fn errors_display() {
        check!(
            super::InvalidKeyLength,
            crate::aes_cbc::Error::IncompleteBlock,
            crate::aes_cbc::Error::InvalidKeyLength,
            crate::aes_ccm::Error::InvalidKeyLength,
            crate::aes_ccm::Error::InvalidNonceLength,
            crate::aes_ccm::Error::InvalidTextLength,
            crate::aes_ccm::Error::TagMismatch,
            crate::aes_ecb::Error::IncompleteBlock,
            crate::aes_ecb::Error::InvalidKeyLength,
            crate::aes_gcm::Error::AadAfterText,
            crate::aes_gcm::Error::InvalidAadLength,
            crate::aes_gcm::Error::InvalidKeyLength,
            crate::aes_gcm::Error::InvalidNonceLength,
            crate::aes_gcm::Error::InvalidOutputLength,
            crate::aes_gcm::Error::InvalidTextLength,
            crate::aes_gcm::Error::TagMismatch,
            crate::aes_gcm::Error::TooManyPieces,
            crate::aes_gcm_siv::Error::InvalidAadLength,
            crate::aes_gcm_siv::Error::InvalidKeyLength,
            crate::aes_gcm_siv::Error::InvalidTextLength,
            crate::aes_gcm_siv::Error::TagMismatch,
            crate::aes_ocb::Error::InvalidKeyLength,
            crate::aes_ocb::Error::InvalidNonceLength,
            crate::aes_ocb::Error::TagMismatch,
            crate::aes_siv::Error::InvalidKeyLength,
            crate::aes_siv::Error::TagMismatch,
            crate::aes_siv::Error::TooManyComponents,
            crate::aes_xts::Error::DataUnitTooLong,
            crate::aes_xts::Error::DataUnitTooShort,
            crate::aes_xts::Error::EqualKeyHalves,
            crate::aes_xts::Error::InvalidKeyLength,
            crate::blowfish_cbc::Error::IncompleteBlock,
            crate::blowfish_cbc::Error::InvalidKeyLength,
            crate::blowfish_ecb::Error::IncompleteBlock,
            crate::blowfish_ecb::Error::InvalidKeyLength,
            crate::blowfish_ecb::Error::OutputTooSmall,
            crate::camellia_cbc::Error::IncompleteBlock,
            crate::camellia_cbc::Error::InvalidKeyLength,
            crate::camellia_ecb::Error::IncompleteBlock,
            crate::camellia_ecb::Error::InvalidKeyLength,
            crate::cast5_ecb::Error::IncompleteBlock,
            crate::cast5_ecb::Error::InvalidKeyLength,
            crate::chacha20poly1305::Error::InvalidOutputLength,
            crate::chacha20poly1305::Error::InvalidTextLength,
            crate::chacha20poly1305::Error::TagMismatch,
            crate::chacha20poly1305::Error::TooManyPieces,
            crate::ed25519::Error::InvalidSignature,
            crate::ed448::Error::ContextTooLong,
            crate::ed448::Error::InvalidSignature,
            crate::hmac::InvalidMac,
            crate::idea_cbc::Error::IncompleteBlock,
            crate::idea_cbc::Error::InvalidKeyLength,
            crate::idea_ecb::Error::IncompleteBlock,
            crate::idea_ecb::Error::InvalidKeyLength,
            crate::mldsa44::Error::ContextTooLong,
            crate::mldsa44::Error::InvalidSignature,
            crate::mldsa44::Error::LoopBound,
            crate::mldsa44::Error::Randomness,
            crate::mldsa65::Error::ContextTooLong,
            crate::mldsa65::Error::InvalidSignature,
            crate::mldsa65::Error::LoopBound,
            crate::mldsa65::Error::Randomness,
            crate::mldsa87::Error::ContextTooLong,
            crate::mldsa87::Error::InvalidSignature,
            crate::mldsa87::Error::LoopBound,
            crate::mldsa87::Error::Randomness,
            crate::mlkem_common::Error::InvalidKey,
            crate::mlkem_common::Error::Randomness,
            crate::mlkem_common::Error::SampleBound,
            crate::rc2_cbc::Error::IncompleteBlock,
            crate::rc2_cbc::Error::InvalidEffectiveBits,
            crate::rc2_cbc::Error::InvalidIvLength,
            crate::rc2_cbc::Error::InvalidKeyLength,
            crate::rc2_cbc::Error::OutputTooSmall,
            crate::rc4::Error::InvalidKeyLength,
            crate::seed_cbc::Error::IncompleteBlock,
            crate::seed_cbc::Error::InvalidKeyLength,
            crate::seed_ecb::Error::IncompleteBlock,
            crate::sm4_cbc::Error::IncompleteBlock,
            crate::sm4_ecb::Error::IncompleteBlock,
            crate::triple_des_cbc::Error::IncompleteBlock,
            crate::triple_des_cbc::Error::InvalidKeyLength,
            crate::triple_des_ecb::Error::IncompleteBlock,
            crate::triple_des_ecb::Error::InvalidKeyLength,
            crate::x25519::Error::Randomness,
            crate::x25519::Error::ZeroSharedSecret,
            crate::x448::Error::Randomness,
            crate::x448::Error::ZeroSharedSecret,
        );
    }
}
