//! RSAES-OAEP's verified functions on PPC64LE: the tables of the hash
//! functions (`crate::arch::fn_tables`), and `vg_rsa_oaep_encrypt_precomputed`
//! and `vg_rsa_oaep_decrypt` (contracts
//! `VG.Spec.RsaOaep.encryptTablesContract` and `decryptTablesContract`),
//! which take the label's hash function and MGF1's as tables, for each
//! implementation of the RSA operations (`crate::rsa::Backend`), which
//! `table::oaep_functions!` chooses from.

#![cfg(all(target_arch = "powerpc64", feature = "alloc"))]

use crate::arch::fn_tables::{self, *};
use crate::arch::rsa_oaep::*;
use crate::hashes::sha1::Sha1Backend;
use crate::hashes::sha224::Sha224Backend;
use crate::hashes::sha256::Sha256Backend;
use crate::hashes::sha384::Sha384Backend;
use crate::hashes::sha512::Sha512Backend;
use crate::hashes::sha512_224::Sha512_224Backend;
use crate::hashes::sha512_256::Sha512_256Backend;
use crate::rsa_pkcs1_sig::Hash;
use verified_garbage_cpu::Features;

/// The table of the hash function `hash` for the implementation that a CPU
/// with the features `f` runs best, with the features its functions need,
/// or `None` if `hash` is not supported.
pub(super) fn hash_table(hash: Hash, f: Features) -> Option<(&'static fn_tables::Hash, Features)> {
    let none = Features(0);
    Some(match hash {
        Hash::Sha1 => match Sha1Backend::select(f) {
            Sha1Backend::Scalar => (&VG_HASH_SHA1, none),
        },
        Hash::Sha224 => match Sha224Backend::select(f) {
            Sha224Backend::Scalar => (&VG_HASH_SHA224, none),
        },
        Hash::Sha256 => match Sha256Backend::select(f) {
            Sha256Backend::Scalar => (&VG_HASH_SHA256, none),
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

crate::rsa_oaep::table::oaep_functions! {
    encrypt: {
        Baseline => vg_rsa_oaep_encrypt_precomputed [],
    },
    decrypt: {
        Baseline => vg_rsa_oaep_decrypt [],
    },
}
