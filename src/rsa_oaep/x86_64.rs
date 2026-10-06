//! The implementations of RSAES-OAEP on x86-64, by pair of hash functions
//! and implementation of each hash function and of the private-key
//! operation.

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
pub(super) const IMPLS: usize = 56 + 168;

/// `vg_rsa_oaep_sha1_mgf1_sha1_encrypt` for the implementations of Sha1 and
/// Sha1 chosen.
pub(super) fn encrypt_sha1_mgf1_sha1(h: Sha1Backend) -> EncryptFn<20> {
    use crate::arch::rsa_oaep_sha1_mgf1_sha1::*;
    match h {
        Sha1Backend::Scalar => vg_rsa_oaep_sha1_mgf1_sha1_encrypt,
        Sha1Backend::ShaNi => vg_rsa_oaep_sha1_mgf1_sha1_encrypt_sha1_shani,
    }
}

/// `vg_rsa_oaep_sha1_mgf1_sha1_decrypt` for the implementations of Sha1,
/// Sha1 and the private-key operation chosen.
pub(super) fn decrypt_sha1_mgf1_sha1(h: Sha1Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha1_mgf1_sha1::*;
    match (h, crt) {
        (Sha1Backend::Scalar, Backend::Baseline) => vg_rsa_oaep_sha1_mgf1_sha1_decrypt,
        (Sha1Backend::Scalar, Backend::Adx) => vg_rsa_oaep_sha1_mgf1_sha1_decrypt_crt_adx,
        (Sha1Backend::Scalar, Backend::Ifma) => vg_rsa_oaep_sha1_mgf1_sha1_decrypt_crt_ifma,
        (Sha1Backend::ShaNi, Backend::Baseline) => vg_rsa_oaep_sha1_mgf1_sha1_decrypt_sha1_shani,
        (Sha1Backend::ShaNi, Backend::Adx) => vg_rsa_oaep_sha1_mgf1_sha1_decrypt_sha1_shani_crt_adx,
        (Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha1_mgf1_sha1_decrypt_sha1_shani_crt_ifma
        }
    }
}

/// `vg_rsa_oaep_sha224_mgf1_sha1_encrypt` for the implementations of Sha224 and
/// Sha1 chosen.
pub(super) fn encrypt_sha224_mgf1_sha1(h: Sha224Backend, g: Sha1Backend) -> EncryptFn<28> {
    use crate::arch::rsa_oaep_sha224_mgf1_sha1::*;
    match (h, g) {
        (Sha224Backend::Scalar, Sha1Backend::Scalar) => vg_rsa_oaep_sha224_mgf1_sha1_encrypt,
        (Sha224Backend::Scalar, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha224_mgf1_sha1_encrypt_mgf1_shani
        }
        (Sha224Backend::ShaNi, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha224_mgf1_sha1_encrypt_sha224_shani
        }
        (Sha224Backend::ShaNi, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha224_mgf1_sha1_encrypt_sha224_shani_mgf1_shani
        }
        (Sha224Backend::Avx2, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha224_mgf1_sha1_encrypt_sha224_avx2
        }
        (Sha224Backend::Avx2, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha224_mgf1_sha1_encrypt_sha224_avx2_mgf1_shani
        }
    }
}

/// `vg_rsa_oaep_sha224_mgf1_sha1_decrypt` for the implementations of Sha224,
/// Sha1 and the private-key operation chosen.
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
        (Sha224Backend::Scalar, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_crt_adx
        }
        (Sha224Backend::Scalar, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_crt_ifma
        }
        (Sha224Backend::Scalar, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_mgf1_shani
        }
        (Sha224Backend::Scalar, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_mgf1_shani_crt_adx
        }
        (Sha224Backend::Scalar, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_mgf1_shani_crt_ifma
        }
        (Sha224Backend::ShaNi, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_shani
        }
        (Sha224Backend::ShaNi, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_shani_crt_adx
        }
        (Sha224Backend::ShaNi, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_shani_crt_ifma
        }
        (Sha224Backend::ShaNi, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_shani_mgf1_shani
        }
        (Sha224Backend::ShaNi, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_shani_mgf1_shani_crt_adx
        }
        (Sha224Backend::ShaNi, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_shani_mgf1_shani_crt_ifma
        }
        (Sha224Backend::Avx2, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_avx2
        }
        (Sha224Backend::Avx2, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_avx2_crt_adx
        }
        (Sha224Backend::Avx2, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_avx2_crt_ifma
        }
        (Sha224Backend::Avx2, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_avx2_mgf1_shani
        }
        (Sha224Backend::Avx2, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_avx2_mgf1_shani_crt_adx
        }
        (Sha224Backend::Avx2, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_avx2_mgf1_shani_crt_ifma
        }
    }
}

/// `vg_rsa_oaep_sha224_mgf1_sha224_encrypt` for the implementations of Sha224 and
/// Sha224 chosen.
pub(super) fn encrypt_sha224_mgf1_sha224(h: Sha224Backend) -> EncryptFn<28> {
    use crate::arch::rsa_oaep_sha224_mgf1_sha224::*;
    match h {
        Sha224Backend::Scalar => vg_rsa_oaep_sha224_mgf1_sha224_encrypt,
        Sha224Backend::ShaNi => vg_rsa_oaep_sha224_mgf1_sha224_encrypt_sha224_shani,
        Sha224Backend::Avx2 => vg_rsa_oaep_sha224_mgf1_sha224_encrypt_sha224_avx2,
    }
}

/// `vg_rsa_oaep_sha224_mgf1_sha224_decrypt` for the implementations of Sha224,
/// Sha224 and the private-key operation chosen.
pub(super) fn decrypt_sha224_mgf1_sha224(h: Sha224Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha224_mgf1_sha224::*;
    match (h, crt) {
        (Sha224Backend::Scalar, Backend::Baseline) => vg_rsa_oaep_sha224_mgf1_sha224_decrypt,
        (Sha224Backend::Scalar, Backend::Adx) => vg_rsa_oaep_sha224_mgf1_sha224_decrypt_crt_adx,
        (Sha224Backend::Scalar, Backend::Ifma) => vg_rsa_oaep_sha224_mgf1_sha224_decrypt_crt_ifma,
        (Sha224Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha224_mgf1_sha224_decrypt_sha224_shani
        }
        (Sha224Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha224_mgf1_sha224_decrypt_sha224_shani_crt_adx
        }
        (Sha224Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha224_mgf1_sha224_decrypt_sha224_shani_crt_ifma
        }
        (Sha224Backend::Avx2, Backend::Baseline) => {
            vg_rsa_oaep_sha224_mgf1_sha224_decrypt_sha224_avx2
        }
        (Sha224Backend::Avx2, Backend::Adx) => {
            vg_rsa_oaep_sha224_mgf1_sha224_decrypt_sha224_avx2_crt_adx
        }
        (Sha224Backend::Avx2, Backend::Ifma) => {
            vg_rsa_oaep_sha224_mgf1_sha224_decrypt_sha224_avx2_crt_ifma
        }
    }
}

/// `vg_rsa_oaep_sha256_mgf1_sha1_encrypt` for the implementations of Sha256 and
/// Sha1 chosen.
pub(super) fn encrypt_sha256_mgf1_sha1(h: Sha256Backend, g: Sha1Backend) -> EncryptFn<32> {
    use crate::arch::rsa_oaep_sha256_mgf1_sha1::*;
    match (h, g) {
        (Sha256Backend::Scalar, Sha1Backend::Scalar) => vg_rsa_oaep_sha256_mgf1_sha1_encrypt,
        (Sha256Backend::Scalar, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha256_mgf1_sha1_encrypt_mgf1_shani
        }
        (Sha256Backend::ShaNi, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha256_mgf1_sha1_encrypt_sha256_shani
        }
        (Sha256Backend::ShaNi, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha256_mgf1_sha1_encrypt_sha256_shani_mgf1_shani
        }
        (Sha256Backend::Avx2, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha256_mgf1_sha1_encrypt_sha256_avx2
        }
        (Sha256Backend::Avx2, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha256_mgf1_sha1_encrypt_sha256_avx2_mgf1_shani
        }
    }
}

/// `vg_rsa_oaep_sha256_mgf1_sha1_decrypt` for the implementations of Sha256,
/// Sha1 and the private-key operation chosen.
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
        (Sha256Backend::Scalar, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_crt_adx
        }
        (Sha256Backend::Scalar, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_crt_ifma
        }
        (Sha256Backend::Scalar, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_mgf1_shani
        }
        (Sha256Backend::Scalar, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_mgf1_shani_crt_adx
        }
        (Sha256Backend::Scalar, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_mgf1_shani_crt_ifma
        }
        (Sha256Backend::ShaNi, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_shani
        }
        (Sha256Backend::ShaNi, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_shani_crt_adx
        }
        (Sha256Backend::ShaNi, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_shani_crt_ifma
        }
        (Sha256Backend::ShaNi, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_shani_mgf1_shani
        }
        (Sha256Backend::ShaNi, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_shani_mgf1_shani_crt_adx
        }
        (Sha256Backend::ShaNi, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_shani_mgf1_shani_crt_ifma
        }
        (Sha256Backend::Avx2, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_avx2
        }
        (Sha256Backend::Avx2, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_avx2_crt_adx
        }
        (Sha256Backend::Avx2, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_avx2_crt_ifma
        }
        (Sha256Backend::Avx2, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_avx2_mgf1_shani
        }
        (Sha256Backend::Avx2, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_avx2_mgf1_shani_crt_adx
        }
        (Sha256Backend::Avx2, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_avx2_mgf1_shani_crt_ifma
        }
    }
}

/// `vg_rsa_oaep_sha256_mgf1_sha256_encrypt` for the implementations of Sha256 and
/// Sha256 chosen.
pub(super) fn encrypt_sha256_mgf1_sha256(h: Sha256Backend) -> EncryptFn<32> {
    use crate::arch::rsa_oaep_sha256_mgf1_sha256::*;
    match h {
        Sha256Backend::Scalar => vg_rsa_oaep_sha256_mgf1_sha256_encrypt,
        Sha256Backend::ShaNi => vg_rsa_oaep_sha256_mgf1_sha256_encrypt_sha256_shani,
        Sha256Backend::Avx2 => vg_rsa_oaep_sha256_mgf1_sha256_encrypt_sha256_avx2,
    }
}

/// `vg_rsa_oaep_sha256_mgf1_sha256_decrypt` for the implementations of Sha256,
/// Sha256 and the private-key operation chosen.
pub(super) fn decrypt_sha256_mgf1_sha256(h: Sha256Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha256_mgf1_sha256::*;
    match (h, crt) {
        (Sha256Backend::Scalar, Backend::Baseline) => vg_rsa_oaep_sha256_mgf1_sha256_decrypt,
        (Sha256Backend::Scalar, Backend::Adx) => vg_rsa_oaep_sha256_mgf1_sha256_decrypt_crt_adx,
        (Sha256Backend::Scalar, Backend::Ifma) => vg_rsa_oaep_sha256_mgf1_sha256_decrypt_crt_ifma,
        (Sha256Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha256_mgf1_sha256_decrypt_sha256_shani
        }
        (Sha256Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha256_mgf1_sha256_decrypt_sha256_shani_crt_adx
        }
        (Sha256Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha256_mgf1_sha256_decrypt_sha256_shani_crt_ifma
        }
        (Sha256Backend::Avx2, Backend::Baseline) => {
            vg_rsa_oaep_sha256_mgf1_sha256_decrypt_sha256_avx2
        }
        (Sha256Backend::Avx2, Backend::Adx) => {
            vg_rsa_oaep_sha256_mgf1_sha256_decrypt_sha256_avx2_crt_adx
        }
        (Sha256Backend::Avx2, Backend::Ifma) => {
            vg_rsa_oaep_sha256_mgf1_sha256_decrypt_sha256_avx2_crt_ifma
        }
    }
}

/// `vg_rsa_oaep_sha384_mgf1_sha1_encrypt` for the implementations of Sha384 and
/// Sha1 chosen.
pub(super) fn encrypt_sha384_mgf1_sha1(h: Sha384Backend, g: Sha1Backend) -> EncryptFn<48> {
    use crate::arch::rsa_oaep_sha384_mgf1_sha1::*;
    match (h, g) {
        (Sha384Backend::Scalar, Sha1Backend::Scalar) => vg_rsa_oaep_sha384_mgf1_sha1_encrypt,
        (Sha384Backend::Scalar, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha384_mgf1_sha1_encrypt_mgf1_shani
        }
        (Sha384Backend::ShaNi, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha384_mgf1_sha1_encrypt_sha384_shani
        }
        (Sha384Backend::ShaNi, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha384_mgf1_sha1_encrypt_sha384_shani_mgf1_shani
        }
        (Sha384Backend::Avx2, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha384_mgf1_sha1_encrypt_sha384_avx2
        }
        (Sha384Backend::Avx2, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha384_mgf1_sha1_encrypt_sha384_avx2_mgf1_shani
        }
    }
}

/// `vg_rsa_oaep_sha384_mgf1_sha1_decrypt` for the implementations of Sha384,
/// Sha1 and the private-key operation chosen.
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
        (Sha384Backend::Scalar, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_crt_adx
        }
        (Sha384Backend::Scalar, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_crt_ifma
        }
        (Sha384Backend::Scalar, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_mgf1_shani
        }
        (Sha384Backend::Scalar, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_mgf1_shani_crt_adx
        }
        (Sha384Backend::Scalar, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_mgf1_shani_crt_ifma
        }
        (Sha384Backend::ShaNi, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_shani
        }
        (Sha384Backend::ShaNi, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_shani_crt_adx
        }
        (Sha384Backend::ShaNi, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_shani_crt_ifma
        }
        (Sha384Backend::ShaNi, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_shani_mgf1_shani
        }
        (Sha384Backend::ShaNi, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_shani_mgf1_shani_crt_adx
        }
        (Sha384Backend::ShaNi, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_shani_mgf1_shani_crt_ifma
        }
        (Sha384Backend::Avx2, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_avx2
        }
        (Sha384Backend::Avx2, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_avx2_crt_adx
        }
        (Sha384Backend::Avx2, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_avx2_crt_ifma
        }
        (Sha384Backend::Avx2, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_avx2_mgf1_shani
        }
        (Sha384Backend::Avx2, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_avx2_mgf1_shani_crt_adx
        }
        (Sha384Backend::Avx2, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_avx2_mgf1_shani_crt_ifma
        }
    }
}

/// `vg_rsa_oaep_sha384_mgf1_sha384_encrypt` for the implementations of Sha384 and
/// Sha384 chosen.
pub(super) fn encrypt_sha384_mgf1_sha384(h: Sha384Backend) -> EncryptFn<48> {
    use crate::arch::rsa_oaep_sha384_mgf1_sha384::*;
    match h {
        Sha384Backend::Scalar => vg_rsa_oaep_sha384_mgf1_sha384_encrypt,
        Sha384Backend::ShaNi => vg_rsa_oaep_sha384_mgf1_sha384_encrypt_sha384_shani,
        Sha384Backend::Avx2 => vg_rsa_oaep_sha384_mgf1_sha384_encrypt_sha384_avx2,
    }
}

/// `vg_rsa_oaep_sha384_mgf1_sha384_decrypt` for the implementations of Sha384,
/// Sha384 and the private-key operation chosen.
pub(super) fn decrypt_sha384_mgf1_sha384(h: Sha384Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha384_mgf1_sha384::*;
    match (h, crt) {
        (Sha384Backend::Scalar, Backend::Baseline) => vg_rsa_oaep_sha384_mgf1_sha384_decrypt,
        (Sha384Backend::Scalar, Backend::Adx) => vg_rsa_oaep_sha384_mgf1_sha384_decrypt_crt_adx,
        (Sha384Backend::Scalar, Backend::Ifma) => vg_rsa_oaep_sha384_mgf1_sha384_decrypt_crt_ifma,
        (Sha384Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha384_mgf1_sha384_decrypt_sha384_shani
        }
        (Sha384Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha384_mgf1_sha384_decrypt_sha384_shani_crt_adx
        }
        (Sha384Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha384_mgf1_sha384_decrypt_sha384_shani_crt_ifma
        }
        (Sha384Backend::Avx2, Backend::Baseline) => {
            vg_rsa_oaep_sha384_mgf1_sha384_decrypt_sha384_avx2
        }
        (Sha384Backend::Avx2, Backend::Adx) => {
            vg_rsa_oaep_sha384_mgf1_sha384_decrypt_sha384_avx2_crt_adx
        }
        (Sha384Backend::Avx2, Backend::Ifma) => {
            vg_rsa_oaep_sha384_mgf1_sha384_decrypt_sha384_avx2_crt_ifma
        }
    }
}

/// `vg_rsa_oaep_sha512_mgf1_sha1_encrypt` for the implementations of Sha512 and
/// Sha1 chosen.
pub(super) fn encrypt_sha512_mgf1_sha1(h: Sha512Backend, g: Sha1Backend) -> EncryptFn<64> {
    use crate::arch::rsa_oaep_sha512_mgf1_sha1::*;
    match (h, g) {
        (Sha512Backend::Scalar, Sha1Backend::Scalar) => vg_rsa_oaep_sha512_mgf1_sha1_encrypt,
        (Sha512Backend::Scalar, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha512_mgf1_sha1_encrypt_mgf1_shani
        }
        (Sha512Backend::ShaNi, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha512_mgf1_sha1_encrypt_sha512_shani
        }
        (Sha512Backend::ShaNi, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha512_mgf1_sha1_encrypt_sha512_shani_mgf1_shani
        }
        (Sha512Backend::Avx2, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha512_mgf1_sha1_encrypt_sha512_avx2
        }
        (Sha512Backend::Avx2, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha512_mgf1_sha1_encrypt_sha512_avx2_mgf1_shani
        }
    }
}

/// `vg_rsa_oaep_sha512_mgf1_sha1_decrypt` for the implementations of Sha512,
/// Sha1 and the private-key operation chosen.
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
        (Sha512Backend::Scalar, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_crt_adx
        }
        (Sha512Backend::Scalar, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_crt_ifma
        }
        (Sha512Backend::Scalar, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_mgf1_shani
        }
        (Sha512Backend::Scalar, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_mgf1_shani_crt_adx
        }
        (Sha512Backend::Scalar, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_mgf1_shani_crt_ifma
        }
        (Sha512Backend::ShaNi, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_shani
        }
        (Sha512Backend::ShaNi, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_shani_crt_adx
        }
        (Sha512Backend::ShaNi, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_shani_crt_ifma
        }
        (Sha512Backend::ShaNi, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_shani_mgf1_shani
        }
        (Sha512Backend::ShaNi, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_shani_mgf1_shani_crt_adx
        }
        (Sha512Backend::ShaNi, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_shani_mgf1_shani_crt_ifma
        }
        (Sha512Backend::Avx2, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_avx2
        }
        (Sha512Backend::Avx2, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_avx2_crt_adx
        }
        (Sha512Backend::Avx2, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_avx2_crt_ifma
        }
        (Sha512Backend::Avx2, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_avx2_mgf1_shani
        }
        (Sha512Backend::Avx2, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_avx2_mgf1_shani_crt_adx
        }
        (Sha512Backend::Avx2, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha512_mgf1_sha1_decrypt_sha512_avx2_mgf1_shani_crt_ifma
        }
    }
}

/// `vg_rsa_oaep_sha512_mgf1_sha512_encrypt` for the implementations of Sha512 and
/// Sha512 chosen.
pub(super) fn encrypt_sha512_mgf1_sha512(h: Sha512Backend) -> EncryptFn<64> {
    use crate::arch::rsa_oaep_sha512_mgf1_sha512::*;
    match h {
        Sha512Backend::Scalar => vg_rsa_oaep_sha512_mgf1_sha512_encrypt,
        Sha512Backend::ShaNi => vg_rsa_oaep_sha512_mgf1_sha512_encrypt_sha512_shani,
        Sha512Backend::Avx2 => vg_rsa_oaep_sha512_mgf1_sha512_encrypt_sha512_avx2,
    }
}

/// `vg_rsa_oaep_sha512_mgf1_sha512_decrypt` for the implementations of Sha512,
/// Sha512 and the private-key operation chosen.
pub(super) fn decrypt_sha512_mgf1_sha512(h: Sha512Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha512_mgf1_sha512::*;
    match (h, crt) {
        (Sha512Backend::Scalar, Backend::Baseline) => vg_rsa_oaep_sha512_mgf1_sha512_decrypt,
        (Sha512Backend::Scalar, Backend::Adx) => vg_rsa_oaep_sha512_mgf1_sha512_decrypt_crt_adx,
        (Sha512Backend::Scalar, Backend::Ifma) => vg_rsa_oaep_sha512_mgf1_sha512_decrypt_crt_ifma,
        (Sha512Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha512_mgf1_sha512_decrypt_sha512_shani
        }
        (Sha512Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha512_mgf1_sha512_decrypt_sha512_shani_crt_adx
        }
        (Sha512Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha512_mgf1_sha512_decrypt_sha512_shani_crt_ifma
        }
        (Sha512Backend::Avx2, Backend::Baseline) => {
            vg_rsa_oaep_sha512_mgf1_sha512_decrypt_sha512_avx2
        }
        (Sha512Backend::Avx2, Backend::Adx) => {
            vg_rsa_oaep_sha512_mgf1_sha512_decrypt_sha512_avx2_crt_adx
        }
        (Sha512Backend::Avx2, Backend::Ifma) => {
            vg_rsa_oaep_sha512_mgf1_sha512_decrypt_sha512_avx2_crt_ifma
        }
    }
}

/// `vg_rsa_oaep_sha512_224_mgf1_sha1_encrypt` for the implementations of Sha512_224 and
/// Sha1 chosen.
pub(super) fn encrypt_sha512_224_mgf1_sha1(h: Sha512_224Backend, g: Sha1Backend) -> EncryptFn<28> {
    use crate::arch::rsa_oaep_sha512_224_mgf1_sha1::*;
    match (h, g) {
        (Sha512_224Backend::Scalar, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_encrypt
        }
        (Sha512_224Backend::Scalar, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_encrypt_mgf1_shani
        }
        (Sha512_224Backend::ShaNi, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_encrypt_sha512_224_shani
        }
        (Sha512_224Backend::ShaNi, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_encrypt_sha512_224_shani_mgf1_shani
        }
        (Sha512_224Backend::Avx2, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_encrypt_sha512_224_avx2
        }
        (Sha512_224Backend::Avx2, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_encrypt_sha512_224_avx2_mgf1_shani
        }
    }
}

/// `vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt` for the implementations of Sha512_224,
/// Sha1 and the private-key operation chosen.
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
        (Sha512_224Backend::Scalar, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_crt_adx
        }
        (Sha512_224Backend::Scalar, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_crt_ifma
        }
        (Sha512_224Backend::Scalar, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_mgf1_shani
        }
        (Sha512_224Backend::Scalar, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_mgf1_shani_crt_adx
        }
        (Sha512_224Backend::Scalar, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_mgf1_shani_crt_ifma
        }
        (Sha512_224Backend::ShaNi, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_shani
        }
        (Sha512_224Backend::ShaNi, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_shani_crt_adx
        }
        (Sha512_224Backend::ShaNi, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_shani_crt_ifma
        }
        (Sha512_224Backend::ShaNi, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_shani_mgf1_shani
        }
        (Sha512_224Backend::ShaNi, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_shani_mgf1_shani_crt_adx
        }
        (Sha512_224Backend::ShaNi, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_shani_mgf1_shani_crt_ifma
        }
        (Sha512_224Backend::Avx2, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_avx2
        }
        (Sha512_224Backend::Avx2, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_avx2_crt_adx
        }
        (Sha512_224Backend::Avx2, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_avx2_crt_ifma
        }
        (Sha512_224Backend::Avx2, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_avx2_mgf1_shani
        }
        (Sha512_224Backend::Avx2, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_avx2_mgf1_shani_crt_adx
        }
        (Sha512_224Backend::Avx2, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha512_224_mgf1_sha1_decrypt_sha512_224_avx2_mgf1_shani_crt_ifma
        }
    }
}

/// `vg_rsa_oaep_sha512_224_mgf1_sha512_224_encrypt` for the implementations of Sha512_224 and
/// Sha512_224 chosen.
pub(super) fn encrypt_sha512_224_mgf1_sha512_224(h: Sha512_224Backend) -> EncryptFn<28> {
    use crate::arch::rsa_oaep_sha512_224_mgf1_sha512_224::*;
    match h {
        Sha512_224Backend::Scalar => vg_rsa_oaep_sha512_224_mgf1_sha512_224_encrypt,
        Sha512_224Backend::ShaNi => vg_rsa_oaep_sha512_224_mgf1_sha512_224_encrypt_sha512_224_shani,
        Sha512_224Backend::Avx2 => vg_rsa_oaep_sha512_224_mgf1_sha512_224_encrypt_sha512_224_avx2,
    }
}

/// `vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt` for the implementations of Sha512_224,
/// Sha512_224 and the private-key operation chosen.
pub(super) fn decrypt_sha512_224_mgf1_sha512_224(h: Sha512_224Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha512_224_mgf1_sha512_224::*;
    match (h, crt) {
        (Sha512_224Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt
        }
        (Sha512_224Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt_crt_adx
        }
        (Sha512_224Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt_crt_ifma
        }
        (Sha512_224Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt_sha512_224_shani
        }
        (Sha512_224Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt_sha512_224_shani_crt_adx
        }
        (Sha512_224Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt_sha512_224_shani_crt_ifma
        }
        (Sha512_224Backend::Avx2, Backend::Baseline) => {
            vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt_sha512_224_avx2
        }
        (Sha512_224Backend::Avx2, Backend::Adx) => {
            vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt_sha512_224_avx2_crt_adx
        }
        (Sha512_224Backend::Avx2, Backend::Ifma) => {
            vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt_sha512_224_avx2_crt_ifma
        }
    }
}

/// `vg_rsa_oaep_sha512_256_mgf1_sha1_encrypt` for the implementations of Sha512_256 and
/// Sha1 chosen.
pub(super) fn encrypt_sha512_256_mgf1_sha1(h: Sha512_256Backend, g: Sha1Backend) -> EncryptFn<32> {
    use crate::arch::rsa_oaep_sha512_256_mgf1_sha1::*;
    match (h, g) {
        (Sha512_256Backend::Scalar, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_encrypt
        }
        (Sha512_256Backend::Scalar, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_encrypt_mgf1_shani
        }
        (Sha512_256Backend::ShaNi, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_encrypt_sha512_256_shani
        }
        (Sha512_256Backend::ShaNi, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_encrypt_sha512_256_shani_mgf1_shani
        }
        (Sha512_256Backend::Avx2, Sha1Backend::Scalar) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_encrypt_sha512_256_avx2
        }
        (Sha512_256Backend::Avx2, Sha1Backend::ShaNi) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_encrypt_sha512_256_avx2_mgf1_shani
        }
    }
}

/// `vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt` for the implementations of Sha512_256,
/// Sha1 and the private-key operation chosen.
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
        (Sha512_256Backend::Scalar, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_crt_adx
        }
        (Sha512_256Backend::Scalar, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_crt_ifma
        }
        (Sha512_256Backend::Scalar, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_mgf1_shani
        }
        (Sha512_256Backend::Scalar, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_mgf1_shani_crt_adx
        }
        (Sha512_256Backend::Scalar, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_mgf1_shani_crt_ifma
        }
        (Sha512_256Backend::ShaNi, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_shani
        }
        (Sha512_256Backend::ShaNi, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_shani_crt_adx
        }
        (Sha512_256Backend::ShaNi, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_shani_crt_ifma
        }
        (Sha512_256Backend::ShaNi, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_shani_mgf1_shani
        }
        (Sha512_256Backend::ShaNi, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_shani_mgf1_shani_crt_adx
        }
        (Sha512_256Backend::ShaNi, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_shani_mgf1_shani_crt_ifma
        }
        (Sha512_256Backend::Avx2, Sha1Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_avx2
        }
        (Sha512_256Backend::Avx2, Sha1Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_avx2_crt_adx
        }
        (Sha512_256Backend::Avx2, Sha1Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_avx2_crt_ifma
        }
        (Sha512_256Backend::Avx2, Sha1Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_avx2_mgf1_shani
        }
        (Sha512_256Backend::Avx2, Sha1Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_avx2_mgf1_shani_crt_adx
        }
        (Sha512_256Backend::Avx2, Sha1Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_avx2_mgf1_shani_crt_ifma
        }
    }
}

/// `vg_rsa_oaep_sha512_256_mgf1_sha512_256_encrypt` for the implementations of Sha512_256 and
/// Sha512_256 chosen.
pub(super) fn encrypt_sha512_256_mgf1_sha512_256(h: Sha512_256Backend) -> EncryptFn<32> {
    use crate::arch::rsa_oaep_sha512_256_mgf1_sha512_256::*;
    match h {
        Sha512_256Backend::Scalar => vg_rsa_oaep_sha512_256_mgf1_sha512_256_encrypt,
        Sha512_256Backend::ShaNi => vg_rsa_oaep_sha512_256_mgf1_sha512_256_encrypt_sha512_256_shani,
        Sha512_256Backend::Avx2 => vg_rsa_oaep_sha512_256_mgf1_sha512_256_encrypt_sha512_256_avx2,
    }
}

/// `vg_rsa_oaep_sha512_256_mgf1_sha512_256_decrypt` for the implementations of Sha512_256,
/// Sha512_256 and the private-key operation chosen.
pub(super) fn decrypt_sha512_256_mgf1_sha512_256(h: Sha512_256Backend, crt: Backend) -> DecryptFn {
    use crate::arch::rsa_oaep_sha512_256_mgf1_sha512_256::*;
    match (h, crt) {
        (Sha512_256Backend::Scalar, Backend::Baseline) => {
            vg_rsa_oaep_sha512_256_mgf1_sha512_256_decrypt
        }
        (Sha512_256Backend::Scalar, Backend::Adx) => {
            vg_rsa_oaep_sha512_256_mgf1_sha512_256_decrypt_crt_adx
        }
        (Sha512_256Backend::Scalar, Backend::Ifma) => {
            vg_rsa_oaep_sha512_256_mgf1_sha512_256_decrypt_crt_ifma
        }
        (Sha512_256Backend::ShaNi, Backend::Baseline) => {
            vg_rsa_oaep_sha512_256_mgf1_sha512_256_decrypt_sha512_256_shani
        }
        (Sha512_256Backend::ShaNi, Backend::Adx) => {
            vg_rsa_oaep_sha512_256_mgf1_sha512_256_decrypt_sha512_256_shani_crt_adx
        }
        (Sha512_256Backend::ShaNi, Backend::Ifma) => {
            vg_rsa_oaep_sha512_256_mgf1_sha512_256_decrypt_sha512_256_shani_crt_ifma
        }
        (Sha512_256Backend::Avx2, Backend::Baseline) => {
            vg_rsa_oaep_sha512_256_mgf1_sha512_256_decrypt_sha512_256_avx2
        }
        (Sha512_256Backend::Avx2, Backend::Adx) => {
            vg_rsa_oaep_sha512_256_mgf1_sha512_256_decrypt_sha512_256_avx2_crt_adx
        }
        (Sha512_256Backend::Avx2, Backend::Ifma) => {
            vg_rsa_oaep_sha512_256_mgf1_sha512_256_decrypt_sha512_256_avx2_crt_ifma
        }
    }
}

/// Every implementation of every pair, each once.
#[cfg(test)]
pub(super) fn all_impls() -> (Vec<Encrypt>, Vec<DecryptFn>) {
    let (mut e, mut d) = (Vec::new(), Vec::new());
    for h in [Sha1Backend::Scalar, Sha1Backend::ShaNi] {
        e.push(Encrypt::L20(encrypt_sha1_mgf1_sha1(h)));
        for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
            d.push(decrypt_sha1_mgf1_sha1(h, crt));
        }
    }
    for h in [
        Sha224Backend::Scalar,
        Sha224Backend::ShaNi,
        Sha224Backend::Avx2,
    ] {
        for g in [Sha1Backend::Scalar, Sha1Backend::ShaNi] {
            e.push(Encrypt::L28(encrypt_sha224_mgf1_sha1(h, g)));
            for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
                d.push(decrypt_sha224_mgf1_sha1(h, g, crt));
            }
        }
    }
    for h in [
        Sha224Backend::Scalar,
        Sha224Backend::ShaNi,
        Sha224Backend::Avx2,
    ] {
        e.push(Encrypt::L28(encrypt_sha224_mgf1_sha224(h)));
        for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
            d.push(decrypt_sha224_mgf1_sha224(h, crt));
        }
    }
    for h in [
        Sha256Backend::Scalar,
        Sha256Backend::ShaNi,
        Sha256Backend::Avx2,
    ] {
        for g in [Sha1Backend::Scalar, Sha1Backend::ShaNi] {
            e.push(Encrypt::L32(encrypt_sha256_mgf1_sha1(h, g)));
            for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
                d.push(decrypt_sha256_mgf1_sha1(h, g, crt));
            }
        }
    }
    for h in [
        Sha256Backend::Scalar,
        Sha256Backend::ShaNi,
        Sha256Backend::Avx2,
    ] {
        e.push(Encrypt::L32(encrypt_sha256_mgf1_sha256(h)));
        for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
            d.push(decrypt_sha256_mgf1_sha256(h, crt));
        }
    }
    for h in [
        Sha384Backend::Scalar,
        Sha384Backend::ShaNi,
        Sha384Backend::Avx2,
    ] {
        for g in [Sha1Backend::Scalar, Sha1Backend::ShaNi] {
            e.push(Encrypt::L48(encrypt_sha384_mgf1_sha1(h, g)));
            for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
                d.push(decrypt_sha384_mgf1_sha1(h, g, crt));
            }
        }
    }
    for h in [
        Sha384Backend::Scalar,
        Sha384Backend::ShaNi,
        Sha384Backend::Avx2,
    ] {
        e.push(Encrypt::L48(encrypt_sha384_mgf1_sha384(h)));
        for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
            d.push(decrypt_sha384_mgf1_sha384(h, crt));
        }
    }
    for h in [
        Sha512Backend::Scalar,
        Sha512Backend::ShaNi,
        Sha512Backend::Avx2,
    ] {
        for g in [Sha1Backend::Scalar, Sha1Backend::ShaNi] {
            e.push(Encrypt::L64(encrypt_sha512_mgf1_sha1(h, g)));
            for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
                d.push(decrypt_sha512_mgf1_sha1(h, g, crt));
            }
        }
    }
    for h in [
        Sha512Backend::Scalar,
        Sha512Backend::ShaNi,
        Sha512Backend::Avx2,
    ] {
        e.push(Encrypt::L64(encrypt_sha512_mgf1_sha512(h)));
        for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
            d.push(decrypt_sha512_mgf1_sha512(h, crt));
        }
    }
    for h in [
        Sha512_224Backend::Scalar,
        Sha512_224Backend::ShaNi,
        Sha512_224Backend::Avx2,
    ] {
        for g in [Sha1Backend::Scalar, Sha1Backend::ShaNi] {
            e.push(Encrypt::L28(encrypt_sha512_224_mgf1_sha1(h, g)));
            for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
                d.push(decrypt_sha512_224_mgf1_sha1(h, g, crt));
            }
        }
    }
    for h in [
        Sha512_224Backend::Scalar,
        Sha512_224Backend::ShaNi,
        Sha512_224Backend::Avx2,
    ] {
        e.push(Encrypt::L28(encrypt_sha512_224_mgf1_sha512_224(h)));
        for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
            d.push(decrypt_sha512_224_mgf1_sha512_224(h, crt));
        }
    }
    for h in [
        Sha512_256Backend::Scalar,
        Sha512_256Backend::ShaNi,
        Sha512_256Backend::Avx2,
    ] {
        for g in [Sha1Backend::Scalar, Sha1Backend::ShaNi] {
            e.push(Encrypt::L32(encrypt_sha512_256_mgf1_sha1(h, g)));
            for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
                d.push(decrypt_sha512_256_mgf1_sha1(h, g, crt));
            }
        }
    }
    for h in [
        Sha512_256Backend::Scalar,
        Sha512_256Backend::ShaNi,
        Sha512_256Backend::Avx2,
    ] {
        e.push(Encrypt::L32(encrypt_sha512_256_mgf1_sha512_256(h)));
        for crt in [Backend::Baseline, Backend::Adx, Backend::Ifma] {
            d.push(decrypt_sha512_256_mgf1_sha512_256(h, crt));
        }
    }
    (e, d)
}
