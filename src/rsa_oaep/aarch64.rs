//! The implementations of RSAES-OAEP on AArch64, by pair of hash functions
//! and implementation of each hash function (the private-key operation has
//! one, the baseline).

#[cfg(test)]
use super::Encrypt;
use super::{DecryptFn, EncryptFn};
use crate::hashes::sha1::Sha1Backend;
use crate::hashes::sha224::Sha224Backend;
use crate::hashes::sha256::Sha256Backend;
use crate::hashes::sha384::Sha384Backend;
use crate::hashes::sha512::Sha512Backend;
use crate::hashes::sha512_224::Sha512_224Backend;
use crate::hashes::sha512_256::Sha512_256Backend;
use crate::rsa::Backend;
#[cfg(test)]
use alloc::vec::Vec;

/// The number of implementations of encryption and decryption.
#[cfg(test)]
pub(super) const IMPLS: usize = 38 + 38;

/// `vg_rsa_oaep_sha1_mgf1_sha1_encrypt` for the implementation of Sha1.
pub(super) fn encrypt_sha1_mgf1_sha1(h: Sha1Backend) -> EncryptFn<20> {
    use crate::arch::rsa_oaep_sha1_mgf1_sha1::*;
    match h {
        Sha1Backend::Scalar => vg_rsa_oaep_sha1_mgf1_sha1_encrypt,
        Sha1Backend::Sha2 => vg_rsa_oaep_sha1_mgf1_sha1_encrypt_sha1_sha2,
    }
}

/// `vg_rsa_oaep_sha1_mgf1_sha1_decrypt` for the implementations of Sha1 and of
/// the private-key operation.
pub(super) fn decrypt_sha1_mgf1_sha1(h: Sha1Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha1_mgf1_sha1::*;
    match (h, crt) {
        (Sha1Backend::Scalar, Backend::Baseline) => vg_rsa_oaep_sha1_mgf1_sha1_decrypt,
        (Sha1Backend::Sha2, Backend::Baseline) => vg_rsa_oaep_sha1_mgf1_sha1_decrypt_sha1_sha2,
    }
}

/// `vg_rsa_oaep_sha224_mgf1_sha1_encrypt` for the implementations of Sha224 and
/// Sha1.
pub(super) fn encrypt_sha224_mgf1_sha1(h: Sha224Backend, g: Sha1Backend) -> EncryptFn<28> {
    use crate::arch::rsa_oaep_sha224_mgf1_sha1::*;
    match (h, g) {
        (Sha224Backend::Scalar, Sha1Backend::Scalar) => vg_rsa_oaep_sha224_mgf1_sha1_encrypt,
        (Sha224Backend::Scalar, Sha1Backend::Sha2) => {
            vg_rsa_oaep_sha224_mgf1_sha1_encrypt_mgf1_sha2
        }
        (Sha224Backend::Sha2, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha224_mgf1_sha1_encrypt_sha224_sha2
        }
        (Sha224Backend::Sha2, Sha1Backend::Sha2) => {
            vg_rsa_oaep_sha224_mgf1_sha1_encrypt_sha224_sha2_mgf1_sha2
        }
    }
}

/// `vg_rsa_oaep_sha224_mgf1_sha1_decrypt` for the implementations of Sha224,
/// Sha1 and the private-key operation.
pub(super) fn decrypt_sha224_mgf1_sha1(
    h: Sha224Backend,
    g: Sha1Backend,
    crt: Backend,
) -> DecryptFn {
    use crate::arch::rsa_oaep_sha224_mgf1_sha1::*;
    match (h, g, crt) {
        (Sha224Backend::Scalar, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt
        }
        (Sha224Backend::Scalar, Sha1Backend::Sha2, Backend::Baseline) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_mgf1_sha2
        }
        (Sha224Backend::Sha2, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_sha2
        }
        (Sha224Backend::Sha2, Sha1Backend::Sha2, Backend::Baseline) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_sha2_mgf1_sha2
        }
    }
}

/// `vg_rsa_oaep_sha224_mgf1_sha224_encrypt` for the implementation of Sha224.
pub(super) fn encrypt_sha224_mgf1_sha224(h: Sha224Backend) -> EncryptFn<28> {
    use crate::arch::rsa_oaep_sha224_mgf1_sha224::*;
    match h {
        Sha224Backend::Scalar => vg_rsa_oaep_sha224_mgf1_sha224_encrypt,
        Sha224Backend::Sha2 => vg_rsa_oaep_sha224_mgf1_sha224_encrypt_sha224_sha2,
    }
}

/// `vg_rsa_oaep_sha224_mgf1_sha224_decrypt` for the implementations of Sha224 and of
/// the private-key operation.
pub(super) fn decrypt_sha224_mgf1_sha224(h: Sha224Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha224_mgf1_sha224::*;
    match (h, crt) {
        (Sha224Backend::Scalar, Backend::Baseline) => vg_rsa_oaep_sha224_mgf1_sha224_decrypt,
        (Sha224Backend::Sha2, Backend::Baseline) => {
            vg_rsa_oaep_sha224_mgf1_sha224_decrypt_sha224_sha2
        }
    }
}

/// `vg_rsa_oaep_sha256_mgf1_sha1_encrypt` for the implementations of Sha256 and
/// Sha1.
pub(super) fn encrypt_sha256_mgf1_sha1(h: Sha256Backend, g: Sha1Backend) -> EncryptFn<32> {
    use crate::arch::rsa_oaep_sha256_mgf1_sha1::*;
    match (h, g) {
        (Sha256Backend::Scalar, Sha1Backend::Scalar) => vg_rsa_oaep_sha256_mgf1_sha1_encrypt,
        (Sha256Backend::Scalar, Sha1Backend::Sha2) => {
            vg_rsa_oaep_sha256_mgf1_sha1_encrypt_mgf1_sha2
        }
        (Sha256Backend::Sha2, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha256_mgf1_sha1_encrypt_sha256_sha2
        }
        (Sha256Backend::Sha2, Sha1Backend::Sha2) => {
            vg_rsa_oaep_sha256_mgf1_sha1_encrypt_sha256_sha2_mgf1_sha2
        }
    }
}

/// `vg_rsa_oaep_sha256_mgf1_sha1_decrypt` for the implementations of Sha256,
/// Sha1 and the private-key operation.
pub(super) fn decrypt_sha256_mgf1_sha1(
    h: Sha256Backend,
    g: Sha1Backend,
    crt: Backend,
) -> DecryptFn {
    use crate::arch::rsa_oaep_sha256_mgf1_sha1::*;
    match (h, g, crt) {
        (Sha256Backend::Scalar, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt
        }
        (Sha256Backend::Scalar, Sha1Backend::Sha2, Backend::Baseline) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_mgf1_sha2
        }
        (Sha256Backend::Sha2, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_sha2
        }
        (Sha256Backend::Sha2, Sha1Backend::Sha2, Backend::Baseline) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_sha2_mgf1_sha2
        }
    }
}

/// `vg_rsa_oaep_sha256_mgf1_sha256_encrypt` for the implementation of Sha256.
pub(super) fn encrypt_sha256_mgf1_sha256(h: Sha256Backend) -> EncryptFn<32> {
    use crate::arch::rsa_oaep_sha256_mgf1_sha256::*;
    match h {
        Sha256Backend::Scalar => vg_rsa_oaep_sha256_mgf1_sha256_encrypt,
        Sha256Backend::Sha2 => vg_rsa_oaep_sha256_mgf1_sha256_encrypt_sha256_sha2,
    }
}

/// `vg_rsa_oaep_sha256_mgf1_sha256_decrypt` for the implementations of Sha256 and of
/// the private-key operation.
pub(super) fn decrypt_sha256_mgf1_sha256(h: Sha256Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha256_mgf1_sha256::*;
    match (h, crt) {
        (Sha256Backend::Scalar, Backend::Baseline) => vg_rsa_oaep_sha256_mgf1_sha256_decrypt,
        (Sha256Backend::Sha2, Backend::Baseline) => {
            vg_rsa_oaep_sha256_mgf1_sha256_decrypt_sha256_sha2
        }
    }
}

/// `vg_rsa_oaep_sha384_mgf1_sha1_encrypt` for the implementations of Sha384 and
/// Sha1.
pub(super) fn encrypt_sha384_mgf1_sha1(h: Sha384Backend, g: Sha1Backend) -> EncryptFn<48> {
    use crate::arch::rsa_oaep_sha384_mgf1_sha1::*;
    match (h, g) {
        (Sha384Backend::Scalar, Sha1Backend::Scalar) => vg_rsa_oaep_sha384_mgf1_sha1_encrypt,
        (Sha384Backend::Scalar, Sha1Backend::Sha2) => {
            vg_rsa_oaep_sha384_mgf1_sha1_encrypt_mgf1_sha2
        }
        (Sha384Backend::Sha3, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha384_mgf1_sha1_encrypt_sha384_sha3
        }
        (Sha384Backend::Sha3, Sha1Backend::Sha2) => {
            vg_rsa_oaep_sha384_mgf1_sha1_encrypt_sha384_sha3_mgf1_sha2
        }
    }
}

/// `vg_rsa_oaep_sha384_mgf1_sha1_decrypt` for the implementations of Sha384,
/// Sha1 and the private-key operation.
pub(super) fn decrypt_sha384_mgf1_sha1(
    h: Sha384Backend,
    g: Sha1Backend,
    crt: Backend,
) -> DecryptFn {
    use crate::arch::rsa_oaep_sha384_mgf1_sha1::*;
    match (h, g, crt) {
        (Sha384Backend::Scalar, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt
        }
        (Sha384Backend::Scalar, Sha1Backend::Sha2, Backend::Baseline) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_mgf1_sha2
        }
        (Sha384Backend::Sha3, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_sha3
        }
        (Sha384Backend::Sha3, Sha1Backend::Sha2, Backend::Baseline) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_sha3_mgf1_sha2
        }
    }
}

/// `vg_rsa_oaep_sha384_mgf1_sha384_encrypt` for the implementation of Sha384.
pub(super) fn encrypt_sha384_mgf1_sha384(h: Sha384Backend) -> EncryptFn<48> {
    use crate::arch::rsa_oaep_sha384_mgf1_sha384::*;
    match h {
        Sha384Backend::Scalar => vg_rsa_oaep_sha384_mgf1_sha384_encrypt,
        Sha384Backend::Sha3 => vg_rsa_oaep_sha384_mgf1_sha384_encrypt_sha384_sha3,
    }
}

/// `vg_rsa_oaep_sha384_mgf1_sha384_decrypt` for the implementations of Sha384 and of
/// the private-key operation.
pub(super) fn decrypt_sha384_mgf1_sha384(h: Sha384Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha384_mgf1_sha384::*;
    match (h, crt) {
        (Sha384Backend::Scalar, Backend::Baseline) => vg_rsa_oaep_sha384_mgf1_sha384_decrypt,
        (Sha384Backend::Sha3, Backend::Baseline) => {
            vg_rsa_oaep_sha384_mgf1_sha384_decrypt_sha384_sha3
        }
    }
}

/// `vg_rsa_oaep_sha512_mgf1_sha1_encrypt` for the implementations of Sha512 and
/// Sha1.
pub(super) fn encrypt_sha512_mgf1_sha1(h: Sha512Backend, g: Sha1Backend) -> EncryptFn<64> {
    use crate::arch::rsa_oaep_sha512_mgf1_sha1::*;
    match (h, g) {
        (Sha512Backend::Scalar, Sha1Backend::Scalar) => vg_rsa_oaep_sha512_mgf1_sha1_encrypt,
        (Sha512Backend::Scalar, Sha1Backend::Sha2) => {
            vg_rsa_oaep_sha512_mgf1_sha1_encrypt_mgf1_sha2
        }
        (Sha512Backend::Sha3, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha512_mgf1_sha1_encrypt_sha512_sha3
        }
        (Sha512Backend::Sha3, Sha1Backend::Sha2) => {
            vg_rsa_oaep_sha512_mgf1_sha1_encrypt_sha512_sha3_mgf1_sha2
        }
    }
}

/// `vg_rsa_oaep_sha512_mgf1_sha1_decrypt` for the implementations of Sha512,
/// Sha1 and the private-key operation.
pub(super) fn decrypt_sha512_mgf1_sha1(
    h: Sha512Backend,
    g: Sha1Backend,
    crt: Backend,
) -> DecryptFn {
    use crate::arch::rsa_oaep_sha512_mgf1_sha1::*;
    match (h, g, crt) {
        (Sha512Backend::Scalar, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt
        }
        (Sha512Backend::Scalar, Sha1Backend::Sha2, Backend::Baseline) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_mgf1_sha2
        }
        (Sha512Backend::Sha3, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_sha3
        }
        (Sha512Backend::Sha3, Sha1Backend::Sha2, Backend::Baseline) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_sha3_mgf1_sha2
        }
    }
}

/// `vg_rsa_oaep_sha512_mgf1_sha512_encrypt` for the implementation of Sha512.
pub(super) fn encrypt_sha512_mgf1_sha512(h: Sha512Backend) -> EncryptFn<64> {
    use crate::arch::rsa_oaep_sha512_mgf1_sha512::*;
    match h {
        Sha512Backend::Scalar => vg_rsa_oaep_sha512_mgf1_sha512_encrypt,
        Sha512Backend::Sha3 => vg_rsa_oaep_sha512_mgf1_sha512_encrypt_sha512_sha3,
    }
}

/// `vg_rsa_oaep_sha512_mgf1_sha512_decrypt` for the implementations of Sha512 and of
/// the private-key operation.
pub(super) fn decrypt_sha512_mgf1_sha512(h: Sha512Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha512_mgf1_sha512::*;
    match (h, crt) {
        (Sha512Backend::Scalar, Backend::Baseline) => vg_rsa_oaep_sha512_mgf1_sha512_decrypt,
        (Sha512Backend::Sha3, Backend::Baseline) => {
            vg_rsa_oaep_sha512_mgf1_sha512_decrypt_sha512_sha3
        }
    }
}

/// `vg_rsa_oaep_sha512_224_mgf1_sha1_encrypt` for the implementations of Sha512_224 and
/// Sha1.
pub(super) fn encrypt_sha512_224_mgf1_sha1(h: Sha512_224Backend, g: Sha1Backend) -> EncryptFn<28> {
    use crate::arch::rsa_oaep_sha512_224_mgf1_sha1::*;
    match (h, g) {
        (Sha512_224Backend::Scalar, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_encrypt
        }
        (Sha512_224Backend::Scalar, Sha1Backend::Sha2) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_encrypt_mgf1_sha2
        }
        (Sha512_224Backend::Sha3, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_encrypt_sha512_224_sha3
        }
        (Sha512_224Backend::Sha3, Sha1Backend::Sha2) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_encrypt_sha512_224_sha3_mgf1_sha2
        }
    }
}

/// `vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt` for the implementations of Sha512_224,
/// Sha1 and the private-key operation.
pub(super) fn decrypt_sha512_224_mgf1_sha1(
    h: Sha512_224Backend,
    g: Sha1Backend,
    crt: Backend,
) -> DecryptFn {
    use crate::arch::rsa_oaep_sha512_224_mgf1_sha1::*;
    match (h, g, crt) {
        (Sha512_224Backend::Scalar, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt
        }
        (Sha512_224Backend::Scalar, Sha1Backend::Sha2, Backend::Baseline) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_mgf1_sha2
        }
        (Sha512_224Backend::Sha3, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_sha3
        }
        (Sha512_224Backend::Sha3, Sha1Backend::Sha2, Backend::Baseline) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_sha3_mgf1_sha2
        }
    }
}

/// `vg_rsa_oaep_sha512_224_mgf1_sha512_224_encrypt` for the implementation of Sha512_224.
pub(super) fn encrypt_sha512_224_mgf1_sha512_224(h: Sha512_224Backend) -> EncryptFn<28> {
    use crate::arch::rsa_oaep_sha512_224_mgf1_sha512_224::*;
    match h {
        Sha512_224Backend::Scalar => vg_rsa_oaep_sha512_224_mgf1_sha512_224_encrypt,
        Sha512_224Backend::Sha3 => vg_rsa_oaep_sha512_224_mgf1_sha512_224_encrypt_sha512_224_sha3,
    }
}

/// `vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt` for the implementations of Sha512_224 and of
/// the private-key operation.
pub(super) fn decrypt_sha512_224_mgf1_sha512_224(h: Sha512_224Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha512_224_mgf1_sha512_224::*;
    match (h, crt) {
        (Sha512_224Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt
        }
        (Sha512_224Backend::Sha3, Backend::Baseline) => {
            vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt_sha512_224_sha3
        }
    }
}

/// `vg_rsa_oaep_sha512_256_mgf1_sha1_encrypt` for the implementations of Sha512_256 and
/// Sha1.
pub(super) fn encrypt_sha512_256_mgf1_sha1(h: Sha512_256Backend, g: Sha1Backend) -> EncryptFn<32> {
    use crate::arch::rsa_oaep_sha512_256_mgf1_sha1::*;
    match (h, g) {
        (Sha512_256Backend::Scalar, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_encrypt
        }
        (Sha512_256Backend::Scalar, Sha1Backend::Sha2) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_encrypt_mgf1_sha2
        }
        (Sha512_256Backend::Sha3, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_encrypt_sha512_256_sha3
        }
        (Sha512_256Backend::Sha3, Sha1Backend::Sha2) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_encrypt_sha512_256_sha3_mgf1_sha2
        }
    }
}

/// `vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt` for the implementations of Sha512_256,
/// Sha1 and the private-key operation.
pub(super) fn decrypt_sha512_256_mgf1_sha1(
    h: Sha512_256Backend,
    g: Sha1Backend,
    crt: Backend,
) -> DecryptFn {
    use crate::arch::rsa_oaep_sha512_256_mgf1_sha1::*;
    match (h, g, crt) {
        (Sha512_256Backend::Scalar, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt
        }
        (Sha512_256Backend::Scalar, Sha1Backend::Sha2, Backend::Baseline) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_mgf1_sha2
        }
        (Sha512_256Backend::Sha3, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_sha3
        }
        (Sha512_256Backend::Sha3, Sha1Backend::Sha2, Backend::Baseline) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_sha3_mgf1_sha2
        }
    }
}

/// `vg_rsa_oaep_sha512_256_mgf1_sha512_256_encrypt` for the implementation of Sha512_256.
pub(super) fn encrypt_sha512_256_mgf1_sha512_256(h: Sha512_256Backend) -> EncryptFn<32> {
    use crate::arch::rsa_oaep_sha512_256_mgf1_sha512_256::*;
    match h {
        Sha512_256Backend::Scalar => vg_rsa_oaep_sha512_256_mgf1_sha512_256_encrypt,
        Sha512_256Backend::Sha3 => vg_rsa_oaep_sha512_256_mgf1_sha512_256_encrypt_sha512_256_sha3,
    }
}

/// `vg_rsa_oaep_sha512_256_mgf1_sha512_256_decrypt` for the implementations of Sha512_256 and of
/// the private-key operation.
pub(super) fn decrypt_sha512_256_mgf1_sha512_256(h: Sha512_256Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha512_256_mgf1_sha512_256::*;
    match (h, crt) {
        (Sha512_256Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_256_mgf1_sha512_256_decrypt
        }
        (Sha512_256Backend::Sha3, Backend::Baseline) => {
            vg_rsa_oaep_sha512_256_mgf1_sha512_256_decrypt_sha512_256_sha3
        }
    }
}

/// Every implementation of every pair, each once.
#[cfg(test)]
pub(super) fn all_impls() -> (Vec<Encrypt>, Vec<DecryptFn>) {
    let (mut e, mut d) = (Vec::new(), Vec::new());
    for h in [Sha1Backend::Scalar, Sha1Backend::Sha2] {
        e.push(Encrypt::L20(encrypt_sha1_mgf1_sha1(h)));
        d.push(decrypt_sha1_mgf1_sha1(h, Backend::Baseline));
    }
    for h in [Sha224Backend::Scalar, Sha224Backend::Sha2] {
        for g in [Sha1Backend::Scalar, Sha1Backend::Sha2] {
            e.push(Encrypt::L28(encrypt_sha224_mgf1_sha1(h, g)));
            d.push(decrypt_sha224_mgf1_sha1(h, g, Backend::Baseline));
        }
    }
    for h in [Sha224Backend::Scalar, Sha224Backend::Sha2] {
        e.push(Encrypt::L28(encrypt_sha224_mgf1_sha224(h)));
        d.push(decrypt_sha224_mgf1_sha224(h, Backend::Baseline));
    }
    for h in [Sha256Backend::Scalar, Sha256Backend::Sha2] {
        for g in [Sha1Backend::Scalar, Sha1Backend::Sha2] {
            e.push(Encrypt::L32(encrypt_sha256_mgf1_sha1(h, g)));
            d.push(decrypt_sha256_mgf1_sha1(h, g, Backend::Baseline));
        }
    }
    for h in [Sha256Backend::Scalar, Sha256Backend::Sha2] {
        e.push(Encrypt::L32(encrypt_sha256_mgf1_sha256(h)));
        d.push(decrypt_sha256_mgf1_sha256(h, Backend::Baseline));
    }
    for h in [Sha384Backend::Scalar, Sha384Backend::Sha3] {
        for g in [Sha1Backend::Scalar, Sha1Backend::Sha2] {
            e.push(Encrypt::L48(encrypt_sha384_mgf1_sha1(h, g)));
            d.push(decrypt_sha384_mgf1_sha1(h, g, Backend::Baseline));
        }
    }
    for h in [Sha384Backend::Scalar, Sha384Backend::Sha3] {
        e.push(Encrypt::L48(encrypt_sha384_mgf1_sha384(h)));
        d.push(decrypt_sha384_mgf1_sha384(h, Backend::Baseline));
    }
    for h in [Sha512Backend::Scalar, Sha512Backend::Sha3] {
        for g in [Sha1Backend::Scalar, Sha1Backend::Sha2] {
            e.push(Encrypt::L64(encrypt_sha512_mgf1_sha1(h, g)));
            d.push(decrypt_sha512_mgf1_sha1(h, g, Backend::Baseline));
        }
    }
    for h in [Sha512Backend::Scalar, Sha512Backend::Sha3] {
        e.push(Encrypt::L64(encrypt_sha512_mgf1_sha512(h)));
        d.push(decrypt_sha512_mgf1_sha512(h, Backend::Baseline));
    }
    for h in [Sha512_224Backend::Scalar, Sha512_224Backend::Sha3] {
        for g in [Sha1Backend::Scalar, Sha1Backend::Sha2] {
            e.push(Encrypt::L28(encrypt_sha512_224_mgf1_sha1(h, g)));
            d.push(decrypt_sha512_224_mgf1_sha1(h, g, Backend::Baseline));
        }
    }
    for h in [Sha512_224Backend::Scalar, Sha512_224Backend::Sha3] {
        e.push(Encrypt::L28(encrypt_sha512_224_mgf1_sha512_224(h)));
        d.push(decrypt_sha512_224_mgf1_sha512_224(h, Backend::Baseline));
    }
    for h in [Sha512_256Backend::Scalar, Sha512_256Backend::Sha3] {
        for g in [Sha1Backend::Scalar, Sha1Backend::Sha2] {
            e.push(Encrypt::L32(encrypt_sha512_256_mgf1_sha1(h, g)));
            d.push(decrypt_sha512_256_mgf1_sha1(h, g, Backend::Baseline));
        }
    }
    for h in [Sha512_256Backend::Scalar, Sha512_256Backend::Sha3] {
        e.push(Encrypt::L32(encrypt_sha512_256_mgf1_sha512_256(h)));
        d.push(decrypt_sha512_256_mgf1_sha512_256(h, Backend::Baseline));
    }
    (e, d)
}
