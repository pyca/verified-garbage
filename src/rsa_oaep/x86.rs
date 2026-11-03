//! RSAES-OAEP's verified functions on x86: the tables of MGF1's hash
//! functions (`crate::arch::fn_tables`), and for each hash function `H` its
//! `vg_rsa_oaep_<H>_mgf1_encrypt_precomputed` and
//! `vg_rsa_oaep_<H>_mgf1_decrypt` (contracts
//! `VG.Spec.RsaOaep.encryptTableContract` and `decryptTableContract`) for
//! each implementation of `H`'s compression function and of the RSA
//! operation (`crate::rsa::Backend`), which `table::oaep_hash!` chooses
//! from.

#![cfg(all(target_arch = "x86", feature = "alloc"))]

use crate::arch::fn_tables::{self, *};
use crate::hashes::sha1::Sha1Backend;
use crate::hashes::sha224::Sha224Backend;
use crate::hashes::sha256::Sha256Backend;
use crate::hashes::sha384::Sha384Backend;
use crate::hashes::sha512::Sha512Backend;
use crate::hashes::sha512_224::Sha512_224Backend;
use crate::hashes::sha512_256::Sha512_256Backend;
use crate::rsa_pkcs1_sig::Hash;
use verified_garbage_cpu::Features;

/// The table of MGF1's hash function `hash` for the implementation that a
/// CPU with the features `f` runs best, with the features its functions
/// need, or `None` if MGF1 over `hash` is not supported.
pub(super) fn mgf1_table(hash: Hash, f: Features) -> Option<(&'static fn_tables::Hash, Features)> {
    let none = Features(0);
    Some(match hash {
        Hash::Sha1 => match Sha1Backend::select(f) {
            Sha1Backend::Scalar => (&VG_HASH_SHA1, none),
            Sha1Backend::ShaNi => (&VG_HASH_SHA1_SHANI, VG_HASH_SHA1_SHANI_FEATURES),
        },
        Hash::Sha224 => match Sha224Backend::select(f) {
            Sha224Backend::Scalar => (&VG_HASH_SHA224, none),
            Sha224Backend::ShaNi => (&VG_HASH_SHA224_SHANI, VG_HASH_SHA224_SHANI_FEATURES),
        },
        Hash::Sha256 => match Sha256Backend::select(f) {
            Sha256Backend::Scalar => (&VG_HASH_SHA256, none),
            Sha256Backend::ShaNi => (&VG_HASH_SHA256_SHANI, VG_HASH_SHA256_SHANI_FEATURES),
        },
        Hash::Sha384 => match Sha384Backend::select(f) {
            Sha384Backend::Scalar => (&VG_HASH_SHA384, none),
        },
        Hash::Sha512 => match Sha512Backend::select(f) {
            Sha512Backend::Scalar => (&VG_HASH_SHA512, none),
        },
        Hash::Sha512_224 => match Sha512_224Backend::select(f) {
            Sha512_224Backend::Scalar => (&VG_HASH_SHA512_224, none),
        },
        Hash::Sha512_256 => match Sha512_256Backend::select(f) {
            Sha512_256Backend::Scalar => (&VG_HASH_SHA512_256, none),
        },
        _ => return None,
    })
}

/// RSAES-OAEP with SHA-1, which takes MGF1's hash function as a table: for
/// each implementation of SHA-1's compression function (`Sha1Backend`) and
/// of the RSA operation.
pub(super) mod sha1 {
    use crate::arch::rsa_oaep_sha1_mgf1::*;
    use crate::hashes::sha1::Sha1Backend;

    crate::rsa_oaep::table::oaep_hash!(20, Sha1Backend {
        Scalar => {
            encrypt: {
                Baseline => vg_rsa_oaep_sha1_mgf1_encrypt_precomputed [],
            },
            decrypt: {
                Baseline => vg_rsa_oaep_sha1_mgf1_decrypt [],
            },
        },
        ShaNi => {
            encrypt: {
                Baseline => vg_rsa_oaep_sha1_mgf1_encrypt_precomputed_sha1_shani [VG_RSA_OAEP_SHA1_MGF1_ENCRYPT_PRECOMPUTED_SHA1_SHANI_FEATURES],
            },
            decrypt: {
                Baseline => vg_rsa_oaep_sha1_mgf1_decrypt_sha1_shani [VG_RSA_OAEP_SHA1_MGF1_DECRYPT_SHA1_SHANI_FEATURES],
            },
        },
    });
}

/// RSAES-OAEP with SHA-224, which takes MGF1's hash function as a table: for
/// each implementation of SHA-224's compression function (`Sha224Backend`) and
/// of the RSA operation.
pub(super) mod sha224 {
    use crate::arch::rsa_oaep_sha224_mgf1::*;
    use crate::hashes::sha224::Sha224Backend;

    crate::rsa_oaep::table::oaep_hash!(28, Sha224Backend {
        Scalar => {
            encrypt: {
                Baseline => vg_rsa_oaep_sha224_mgf1_encrypt_precomputed [],
            },
            decrypt: {
                Baseline => vg_rsa_oaep_sha224_mgf1_decrypt [],
            },
        },
        ShaNi => {
            encrypt: {
                Baseline => vg_rsa_oaep_sha224_mgf1_encrypt_precomputed_sha256_shani [VG_RSA_OAEP_SHA224_MGF1_ENCRYPT_PRECOMPUTED_SHA256_SHANI_FEATURES],
            },
            decrypt: {
                Baseline => vg_rsa_oaep_sha224_mgf1_decrypt_sha256_shani [VG_RSA_OAEP_SHA224_MGF1_DECRYPT_SHA256_SHANI_FEATURES],
            },
        },
    });
}

/// RSAES-OAEP with SHA-256, which takes MGF1's hash function as a table: for
/// each implementation of SHA-256's compression function (`Sha256Backend`) and
/// of the RSA operation.
pub(super) mod sha256 {
    use crate::arch::rsa_oaep_sha256_mgf1::*;
    use crate::hashes::sha256::Sha256Backend;

    crate::rsa_oaep::table::oaep_hash!(32, Sha256Backend {
        Scalar => {
            encrypt: {
                Baseline => vg_rsa_oaep_sha256_mgf1_encrypt_precomputed [],
            },
            decrypt: {
                Baseline => vg_rsa_oaep_sha256_mgf1_decrypt [],
            },
        },
        ShaNi => {
            encrypt: {
                Baseline => vg_rsa_oaep_sha256_mgf1_encrypt_precomputed_sha256_shani [VG_RSA_OAEP_SHA256_MGF1_ENCRYPT_PRECOMPUTED_SHA256_SHANI_FEATURES],
            },
            decrypt: {
                Baseline => vg_rsa_oaep_sha256_mgf1_decrypt_sha256_shani [VG_RSA_OAEP_SHA256_MGF1_DECRYPT_SHA256_SHANI_FEATURES],
            },
        },
    });
}

/// RSAES-OAEP with SHA-384, which takes MGF1's hash function as a table: for
/// each implementation of SHA-384's compression function (`Sha384Backend`) and
/// of the RSA operation.
pub(super) mod sha384 {
    use crate::arch::rsa_oaep_sha384_mgf1::*;
    use crate::hashes::sha384::Sha384Backend;

    crate::rsa_oaep::table::oaep_hash!(48, Sha384Backend {
        Scalar => {
            encrypt: {
                Baseline => vg_rsa_oaep_sha384_mgf1_encrypt_precomputed [],
            },
            decrypt: {
                Baseline => vg_rsa_oaep_sha384_mgf1_decrypt [],
            },
        },
    });
}

/// RSAES-OAEP with SHA-512, which takes MGF1's hash function as a table: for
/// each implementation of SHA-512's compression function (`Sha512Backend`) and
/// of the RSA operation.
pub(super) mod sha512 {
    use crate::arch::rsa_oaep_sha512_mgf1::*;
    use crate::hashes::sha512::Sha512Backend;

    crate::rsa_oaep::table::oaep_hash!(64, Sha512Backend {
        Scalar => {
            encrypt: {
                Baseline => vg_rsa_oaep_sha512_mgf1_encrypt_precomputed [],
            },
            decrypt: {
                Baseline => vg_rsa_oaep_sha512_mgf1_decrypt [],
            },
        },
    });
}

/// RSAES-OAEP with SHA-512/224, which takes MGF1's hash function as a table: for
/// each implementation of SHA-512/224's compression function (`Sha512_224Backend`) and
/// of the RSA operation.
pub(super) mod sha512_224 {
    use crate::arch::rsa_oaep_sha512_224_mgf1::*;
    use crate::hashes::sha512_224::Sha512_224Backend;

    crate::rsa_oaep::table::oaep_hash!(28, Sha512_224Backend {
        Scalar => {
            encrypt: {
                Baseline => vg_rsa_oaep_sha512_224_mgf1_encrypt_precomputed [],
            },
            decrypt: {
                Baseline => vg_rsa_oaep_sha512_224_mgf1_decrypt [],
            },
        },
    });
}

/// RSAES-OAEP with SHA-512/256, which takes MGF1's hash function as a table: for
/// each implementation of SHA-512/256's compression function (`Sha512_256Backend`) and
/// of the RSA operation.
pub(super) mod sha512_256 {
    use crate::arch::rsa_oaep_sha512_256_mgf1::*;
    use crate::hashes::sha512_256::Sha512_256Backend;

    crate::rsa_oaep::table::oaep_hash!(32, Sha512_256Backend {
        Scalar => {
            encrypt: {
                Baseline => vg_rsa_oaep_sha512_256_mgf1_encrypt_precomputed [],
            },
            decrypt: {
                Baseline => vg_rsa_oaep_sha512_256_mgf1_decrypt [],
            },
        },
    });
}
