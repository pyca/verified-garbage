//! RSASSA-PSS's verified functions on AArch64: the tables of the hash
//! functions (`crate::arch::fn_tables`), and `vg_rsa_pss_sign` and
//! `vg_rsa_pss_verify_precomputed` (contracts
//! `VG.Spec.RsaPss.signTableContract` and `verifyPrecomputedTableContract`),
//! which take the hash function and MGF1's as tables, for each
//! implementation of the RSA operations (`crate::rsa::Backend`), which
//! `table::pss_functions!` chooses from.

#![cfg(all(target_arch = "aarch64", feature = "alloc"))]

use super::Hash;
use crate::arch::fn_tables::{
    self, VG_HASH_MD5, VG_HASH_SHA1, VG_HASH_SHA1_SHA2, VG_HASH_SHA1_SHA2_FEATURES, VG_HASH_SHA224,
    VG_HASH_SHA224_SHA2, VG_HASH_SHA224_SHA2_FEATURES, VG_HASH_SHA256, VG_HASH_SHA256_SHA2,
    VG_HASH_SHA256_SHA2_FEATURES, VG_HASH_SHA384, VG_HASH_SHA384_SHA3,
    VG_HASH_SHA384_SHA3_FEATURES, VG_HASH_SHA512, VG_HASH_SHA512_224, VG_HASH_SHA512_224_SHA3,
    VG_HASH_SHA512_224_SHA3_FEATURES, VG_HASH_SHA512_256, VG_HASH_SHA512_256_SHA3,
    VG_HASH_SHA512_256_SHA3_FEATURES, VG_HASH_SHA512_SHA3, VG_HASH_SHA512_SHA3_FEATURES,
    VG_MD_HASH_MD5, VG_MD_HASH_SHA1, VG_MD_HASH_SHA1_SHA2, VG_MD_HASH_SHA1_SHA2_FEATURES,
    VG_MD_HASH_SHA224, VG_MD_HASH_SHA224_SHA2, VG_MD_HASH_SHA224_SHA2_FEATURES, VG_MD_HASH_SHA256,
    VG_MD_HASH_SHA256_SHA2, VG_MD_HASH_SHA256_SHA2_FEATURES, VG_MD_HASH_SHA384,
    VG_MD_HASH_SHA384_SHA3, VG_MD_HASH_SHA384_SHA3_FEATURES, VG_MD_HASH_SHA512,
    VG_MD_HASH_SHA512_224, VG_MD_HASH_SHA512_224_SHA3, VG_MD_HASH_SHA512_224_SHA3_FEATURES,
    VG_MD_HASH_SHA512_256, VG_MD_HASH_SHA512_256_SHA3, VG_MD_HASH_SHA512_256_SHA3_FEATURES,
    VG_MD_HASH_SHA512_SHA3, VG_MD_HASH_SHA512_SHA3_FEATURES,
};
use crate::arch::rsa_pss::{vg_rsa_pss_sign, vg_rsa_pss_verify_precomputed};
use crate::hashes::sha1::Sha1Backend;
use crate::hashes::sha224::Sha224Backend;
use crate::hashes::sha256::Sha256Backend;
use crate::hashes::sha384::Sha384Backend;
use crate::hashes::sha512::Sha512Backend;
use crate::hashes::sha512_224::Sha512_224Backend;
use crate::hashes::sha512_256::Sha512_256Backend;
use verified_garbage_cpu::Features;

/// The table of `MdHash` of the hash function `hash` for the implementation
/// that a CPU with the features `f` runs best, with the features its
/// functions need.
pub(super) fn md_hash_table(hash: Hash, f: Features) -> (&'static fn_tables::MdHash, Features) {
    let none = Features(0);
    match hash {
        Hash::Md5 => (&VG_MD_HASH_MD5, none),
        Hash::Sha1 => match Sha1Backend::select(f) {
            Sha1Backend::Scalar => (&VG_MD_HASH_SHA1, none),
            Sha1Backend::Sha2 => (&VG_MD_HASH_SHA1_SHA2, VG_MD_HASH_SHA1_SHA2_FEATURES),
        },
        Hash::Sha224 => match Sha224Backend::select(f) {
            Sha224Backend::Scalar => (&VG_MD_HASH_SHA224, none),
            Sha224Backend::Sha2 => (&VG_MD_HASH_SHA224_SHA2, VG_MD_HASH_SHA224_SHA2_FEATURES),
        },
        Hash::Sha256 => match Sha256Backend::select(f) {
            Sha256Backend::Scalar => (&VG_MD_HASH_SHA256, none),
            Sha256Backend::Sha2 => (&VG_MD_HASH_SHA256_SHA2, VG_MD_HASH_SHA256_SHA2_FEATURES),
        },
        Hash::Sha384 => match Sha384Backend::select(f) {
            Sha384Backend::Scalar => (&VG_MD_HASH_SHA384, none),
            Sha384Backend::Sha3 => (&VG_MD_HASH_SHA384_SHA3, VG_MD_HASH_SHA384_SHA3_FEATURES),
        },
        Hash::Sha512 => match Sha512Backend::select(f) {
            Sha512Backend::Scalar => (&VG_MD_HASH_SHA512, none),
            Sha512Backend::Sha3 => (&VG_MD_HASH_SHA512_SHA3, VG_MD_HASH_SHA512_SHA3_FEATURES),
        },
        Hash::Sha512_224 => match Sha512_224Backend::select(f) {
            Sha512_224Backend::Scalar => (&VG_MD_HASH_SHA512_224, none),
            Sha512_224Backend::Sha3 => (
                &VG_MD_HASH_SHA512_224_SHA3,
                VG_MD_HASH_SHA512_224_SHA3_FEATURES,
            ),
        },
        Hash::Sha512_256 => match Sha512_256Backend::select(f) {
            Sha512_256Backend::Scalar => (&VG_MD_HASH_SHA512_256, none),
            Sha512_256Backend::Sha3 => (
                &VG_MD_HASH_SHA512_256_SHA3,
                VG_MD_HASH_SHA512_256_SHA3_FEATURES,
            ),
        },
    }
}

/// The table of `Hash` of the hash function `hash` for the implementation
/// that a CPU with the features `f` runs best, with the features its
/// functions need.
pub(super) fn hash_table(hash: Hash, f: Features) -> (&'static fn_tables::Hash, Features) {
    let none = Features(0);
    match hash {
        Hash::Md5 => (&VG_HASH_MD5, none),
        Hash::Sha1 => match Sha1Backend::select(f) {
            Sha1Backend::Scalar => (&VG_HASH_SHA1, none),
            Sha1Backend::Sha2 => (&VG_HASH_SHA1_SHA2, VG_HASH_SHA1_SHA2_FEATURES),
        },
        Hash::Sha224 => match Sha224Backend::select(f) {
            Sha224Backend::Scalar => (&VG_HASH_SHA224, none),
            Sha224Backend::Sha2 => (&VG_HASH_SHA224_SHA2, VG_HASH_SHA224_SHA2_FEATURES),
        },
        Hash::Sha256 => match Sha256Backend::select(f) {
            Sha256Backend::Scalar => (&VG_HASH_SHA256, none),
            Sha256Backend::Sha2 => (&VG_HASH_SHA256_SHA2, VG_HASH_SHA256_SHA2_FEATURES),
        },
        Hash::Sha384 => match Sha384Backend::select(f) {
            Sha384Backend::Scalar => (&VG_HASH_SHA384, none),
            Sha384Backend::Sha3 => (&VG_HASH_SHA384_SHA3, VG_HASH_SHA384_SHA3_FEATURES),
        },
        Hash::Sha512 => match Sha512Backend::select(f) {
            Sha512Backend::Scalar => (&VG_HASH_SHA512, none),
            Sha512Backend::Sha3 => (&VG_HASH_SHA512_SHA3, VG_HASH_SHA512_SHA3_FEATURES),
        },
        Hash::Sha512_224 => match Sha512_224Backend::select(f) {
            Sha512_224Backend::Scalar => (&VG_HASH_SHA512_224, none),
            Sha512_224Backend::Sha3 => (&VG_HASH_SHA512_224_SHA3, VG_HASH_SHA512_224_SHA3_FEATURES),
        },
        Hash::Sha512_256 => match Sha512_256Backend::select(f) {
            Sha512_256Backend::Scalar => (&VG_HASH_SHA512_256, none),
            Sha512_256Backend::Sha3 => (&VG_HASH_SHA512_256_SHA3, VG_HASH_SHA512_256_SHA3_FEATURES),
        },
    }
}

super::table::pss_functions! {
    sign: {
        Baseline => vg_rsa_pss_sign [],
    },
    verify: {
        Baseline => vg_rsa_pss_verify_precomputed [],
    },
}
