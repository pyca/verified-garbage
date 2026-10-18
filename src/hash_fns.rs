//! Hash functions passed to the verified functions as tables of their
//! streaming functions (`VG.Spec.HashFns`).
//!
//! A verified function taking a hash function as an argument (e.g.
//! `vg_rsa_oaep_decrypt`) takes its number, and a pointer to a table of the
//! addresses of its streaming `init`, `update` and `finalize`, which it
//! calls: `vg_<hash>_init`, `vg_<hash>_update_scratch` and
//! `vg_<hash>_finalize_scratch` (SHA-224's `update` and `finalize` are
//! SHA-256's, and the SHA-512 family's SHA-512's), whose contracts imply
//! `VG.Spec.HashFns.initContract`, `updateContract` and `finalizeContract`
//! with `VG.Spec.HashFns.fnStack` bytes of stack. [`table`] chooses the
//! implementations of their compression functions this CPU runs best, as
//! each hash function's streaming backend does, so the caller has one copy
//! for every hash function and every implementation of it.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use crate::arch::sha1::{
    VG_SHA1_FINALIZE_SCRATCH_SHANI_FEATURES, VG_SHA1_UPDATE_SCRATCH_SHANI_FEATURES,
    vg_sha1_finalize_scratch, vg_sha1_finalize_scratch_shani, vg_sha1_init, vg_sha1_update_scratch,
    vg_sha1_update_scratch_shani,
};
use crate::arch::sha256::{
    VG_SHA256_FINALIZE_SCRATCH_AVX2_FEATURES, VG_SHA256_FINALIZE_SCRATCH_SHANI_FEATURES,
    VG_SHA256_UPDATE_SCRATCH_AVX2_FEATURES, VG_SHA256_UPDATE_SCRATCH_SHANI_FEATURES,
    vg_sha224_init, vg_sha256_finalize_scratch, vg_sha256_finalize_scratch_avx2,
    vg_sha256_finalize_scratch_shani, vg_sha256_init, vg_sha256_update_scratch,
    vg_sha256_update_scratch_avx2, vg_sha256_update_scratch_shani,
};
use crate::arch::sha512::{
    VG_SHA512_FINALIZE_SCRATCH_AVX2_FEATURES, VG_SHA512_FINALIZE_SCRATCH_SHANI_FEATURES,
    VG_SHA512_UPDATE_SCRATCH_AVX2_FEATURES, VG_SHA512_UPDATE_SCRATCH_SHANI_FEATURES,
    vg_sha384_init, vg_sha512_224_init, vg_sha512_256_init, vg_sha512_finalize_scratch,
    vg_sha512_finalize_scratch_avx2, vg_sha512_finalize_scratch_shani, vg_sha512_init,
    vg_sha512_update_scratch, vg_sha512_update_scratch_avx2, vg_sha512_update_scratch_shani,
};
use crate::cpu::Features;
use crate::hashes::sha1::Sha1Backend;
use crate::hashes::sha224::Sha224Backend;
use crate::hashes::sha256::Sha256Backend;
use crate::hashes::sha384::Sha384Backend;
use crate::hashes::sha512::Sha512Backend;
use crate::hashes::sha512_224::Sha512_224Backend;
use crate::hashes::sha512_256::Sha512_256Backend;
use crate::rsa_pkcs1_sig::Hash;

/// A hash function as the verified functions take it: its number
/// (`VG.Spec.HashId`) and the table of its streaming functions.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Table {
    /// The hash function's number, `hash` (`Hash as usize`).
    pub(crate) id: usize,
    /// The addresses of its `init`, `update` and `finalize`.
    pub(crate) fns: [u64; 3],
}

/// The address of a function, as a table holds it.
macro_rules! addrs {
    ($($f:path),* $(,)?) => {
        [$($f as *const () as usize as u64),*]
    };
}

/// SHA-1's, SHA-256's or SHA-512's update and finalize for an
/// implementation, with `init` from the hash function itself.
macro_rules! entry {
    ($init:path, $update:path, $finalize:path, [$($req:path),*]) => {
        (addrs!($init, $update, $finalize), Features::all(&[$($req),*]))
    };
}

/// The SHA-256 functions with the initial hash value of `init` (SHA-256's
/// or SHA-224's), for the implementation `v` of the compression function.
macro_rules! sha256_family {
    ($backend:ident, $f:expr, $init:path) => {
        match $backend::select($f) {
            $backend::Scalar => entry!(
                $init,
                vg_sha256_update_scratch,
                vg_sha256_finalize_scratch,
                []
            ),
            $backend::ShaNi => entry!(
                $init,
                vg_sha256_update_scratch_shani,
                vg_sha256_finalize_scratch_shani,
                [
                    VG_SHA256_UPDATE_SCRATCH_SHANI_FEATURES,
                    VG_SHA256_FINALIZE_SCRATCH_SHANI_FEATURES
                ]
            ),
            $backend::Avx2 => entry!(
                $init,
                vg_sha256_update_scratch_avx2,
                vg_sha256_finalize_scratch_avx2,
                [
                    VG_SHA256_UPDATE_SCRATCH_AVX2_FEATURES,
                    VG_SHA256_FINALIZE_SCRATCH_AVX2_FEATURES
                ]
            ),
        }
    };
}

/// The SHA-512 functions with the initial hash value of `init`.
macro_rules! sha512_family {
    ($backend:ident, $f:expr, $init:path) => {
        match $backend::select($f) {
            $backend::Scalar => entry!(
                $init,
                vg_sha512_update_scratch,
                vg_sha512_finalize_scratch,
                []
            ),
            $backend::ShaNi => entry!(
                $init,
                vg_sha512_update_scratch_shani,
                vg_sha512_finalize_scratch_shani,
                [
                    VG_SHA512_UPDATE_SCRATCH_SHANI_FEATURES,
                    VG_SHA512_FINALIZE_SCRATCH_SHANI_FEATURES
                ]
            ),
            $backend::Avx2 => entry!(
                $init,
                vg_sha512_update_scratch_avx2,
                vg_sha512_finalize_scratch_avx2,
                [
                    VG_SHA512_UPDATE_SCRATCH_AVX2_FEATURES,
                    VG_SHA512_FINALIZE_SCRATCH_AVX2_FEATURES
                ]
            ),
        }
    };
}

/// The table of `hash`'s streaming functions for the implementations a CPU
/// with the features `f` runs best, or `None` for a hash function with no
/// such functions (MD5, which no caller takes, and SHA-3). The functions
/// need no CPU feature their backend was not chosen for (checked here, on
/// every set of features in the tests).
pub(crate) fn table(hash: Hash, f: Features) -> Option<Table> {
    let (fns, features) = match hash {
        Hash::Sha1 => match Sha1Backend::select(f) {
            Sha1Backend::Scalar => {
                entry!(
                    vg_sha1_init,
                    vg_sha1_update_scratch,
                    vg_sha1_finalize_scratch,
                    []
                )
            }
            Sha1Backend::ShaNi => entry!(
                vg_sha1_init,
                vg_sha1_update_scratch_shani,
                vg_sha1_finalize_scratch_shani,
                [
                    VG_SHA1_UPDATE_SCRATCH_SHANI_FEATURES,
                    VG_SHA1_FINALIZE_SCRATCH_SHANI_FEATURES
                ]
            ),
        },
        Hash::Sha224 => sha256_family!(Sha224Backend, f, vg_sha224_init),
        Hash::Sha256 => sha256_family!(Sha256Backend, f, vg_sha256_init),
        Hash::Sha384 => sha512_family!(Sha384Backend, f, vg_sha384_init),
        Hash::Sha512 => sha512_family!(Sha512Backend, f, vg_sha512_init),
        Hash::Sha512_224 => sha512_family!(Sha512_224Backend, f, vg_sha512_224_init),
        Hash::Sha512_256 => sha512_family!(Sha512_256Backend, f, vg_sha512_256_init),
        Hash::Md5 | Hash::Sha3_224 | Hash::Sha3_256 | Hash::Sha3_384 | Hash::Sha3_512 => {
            return None;
        }
    };
    debug_assert!(f.contains(features), "{hash:?}");
    Some(Table {
        id: hash as usize,
        fns,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The functions of each table need no CPU feature that their backend
    /// was not chosen for (`table`'s check), on every set of features; and
    /// only the SHA-1 and SHA-2 functions have tables.
    #[test]
    fn features() {
        for bits in 0..1u32 << crate::cpu::NAMES.len() {
            let f = Features(bits);
            for hash in [
                Hash::Md5,
                Hash::Sha1,
                Hash::Sha224,
                Hash::Sha256,
                Hash::Sha384,
                Hash::Sha512,
                Hash::Sha512_224,
                Hash::Sha512_256,
                Hash::Sha3_224,
                Hash::Sha3_256,
                Hash::Sha3_384,
                Hash::Sha3_512,
            ] {
                match table(hash, f) {
                    Some(t) => assert_eq!(t.id, hash as usize),
                    None => assert!(matches!(
                        hash,
                        Hash::Md5
                            | Hash::Sha3_224
                            | Hash::Sha3_256
                            | Hash::Sha3_384
                            | Hash::Sha3_512
                    )),
                }
            }
        }
    }
}
