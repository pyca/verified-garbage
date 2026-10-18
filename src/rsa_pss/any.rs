//! RSASSA-PSS on x86-64: the verified `vg_rsa_pss_sign` and
//! `vg_rsa_pss_verify_precomputed` (contracts `VG.Spec.RsaPss.signAnyContract`
//! and `verifyAnyContract`), which take both hash functions as tables of their
//! streaming functions (`crate::hash_fns`), for each implementation of the
//! RSA operation (`crate::rsa::Backend`).

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use super::{Hash, public_scratch_words, scratch_words};
use crate::arch::rsa_pss::{
    vg_rsa_pss_sign, vg_rsa_pss_sign_adx, vg_rsa_pss_sign_ifma, vg_rsa_pss_verify_precomputed,
    vg_rsa_pss_verify_precomputed_adx, vg_rsa_pss_verify_precomputed_ifma,
};
use crate::cpu::detected;
use crate::hash_fns::{Table, table};
use crate::rsa::{Backend, PrivateKey, PublicKey};
use crate::rsa_pkcs1_sig;

/// The table of `hash`'s streaming functions for this CPU's
/// implementations, numbered as `VG.Spec.HashId` numbers them.
fn table_of(hash: Hash) -> Table {
    let h = match hash {
        Hash::Md5 => rsa_pkcs1_sig::Hash::Md5,
        Hash::Sha1 => rsa_pkcs1_sig::Hash::Sha1,
        Hash::Sha224 => rsa_pkcs1_sig::Hash::Sha224,
        Hash::Sha256 => rsa_pkcs1_sig::Hash::Sha256,
        Hash::Sha384 => rsa_pkcs1_sig::Hash::Sha384,
        Hash::Sha512 => rsa_pkcs1_sig::Hash::Sha512,
        Hash::Sha512_224 => rsa_pkcs1_sig::Hash::Sha512_224,
        Hash::Sha512_256 => rsa_pkcs1_sig::Hash::Sha512_256,
    };
    table(h, detected()).expect("MD5, SHA-1 and the SHA-2 functions have tables")
}

/// `vg_rsa_pss_sign` for the RSA operation this CPU runs best, on the key,
/// the hash value of `hash` (as long as its values), the salt, the
/// modulus-long `out` and the working space, with MGF1 over `mgf1_hash`.
pub(super) fn sign(
    out: &mut [u8],
    key: &PrivateKey,
    digest: &[u8],
    hash: Hash,
    mgf1_hash: Hash,
    salt: &[u8],
    scratch: &mut [u64],
) -> u32 {
    let (h, g) = (table_of(hash), table_of(mgf1_hash));
    let f = match Backend::select(detected()) {
        Backend::Baseline => vg_rsa_pss_sign,
        // `select` chose them because the CPU has the features they need.
        Backend::Adx => vg_rsa_pss_sign_adx,
        Backend::Ifma => vg_rsa_pss_sign_ifma,
    };
    assert!(
        digest.len() == hash.digest_len()
            && out.len() == key.n.len()
            && scratch.len() == scratch_words(key.n.len())
    );
    // SAFETY: each pointer is valid for its length (`out` for writes,
    // `scratch` too), and none overlaps another or wraps around, as they
    // are distinct Rust allocations; `PrivateKey::from_crt` gives
    // `64 ≤ n_len ≤ 1024`, `1 ≤ e_len ≤ 5 ≤ n_len`, `1 ≤ p_len < n_len`,
    // `1 ≤ q_len < n_len`, `dp_len = qinv_len = p_len` and `dq_len = q_len`;
    // `out_len = n_len`, `digest_len` is the length of `hash`'s values and
    // `scratch_len = 16 n_len + 1056`; `hash` and `mgf1_hash` are the
    // numbers of MD5, SHA-1 or SHA-2 functions, and `h.fns` and `g.fns`
    // their streaming functions, for implementations the CPU can run
    // (`table`); and the CPU has the features of `f`, which `select` chose.
    unsafe {
        f(
            out.as_mut_ptr(),
            out.len(),
            key.n.as_ptr(),
            key.n.len(),
            key.e.as_ptr(),
            key.e.len(),
            key.p.as_ptr(),
            key.p.len(),
            key.q.as_ptr(),
            key.q.len(),
            key.dp.as_ptr(),
            key.dp.len(),
            key.dq.as_ptr(),
            key.dq.len(),
            key.qinv.as_ptr(),
            key.qinv.len(),
            digest.as_ptr(),
            digest.len(),
            salt.as_ptr(),
            salt.len(),
            scratch.as_mut_ptr(),
            scratch.len(),
            h.id,
            g.id,
            &h.fns,
            &g.fns,
        )
    }
}

/// `vg_rsa_pss_verify_precomputed` for the RSA operation this CPU runs
/// best, on the key, the modulus-long signature, the hash value of `hash`
/// (as long as its values), the salt length and whether any is allowed,
/// and the working space, with MGF1 over `mgf1_hash`.
#[allow(clippy::too_many_arguments)]
pub(super) fn verify(
    key: &PublicKey,
    signature: &[u8],
    digest: &[u8],
    hash: Hash,
    mgf1_hash: Hash,
    salt_len: usize,
    any: u32,
    scratch: &mut [u64],
) -> u32 {
    let (h, g) = (table_of(hash), table_of(mgf1_hash));
    let f = match Backend::select(detected()) {
        Backend::Baseline => vg_rsa_pss_verify_precomputed,
        // `select` chose them because the CPU has the features they need.
        Backend::Adx => vg_rsa_pss_verify_precomputed_adx,
        Backend::Ifma => vg_rsa_pss_verify_precomputed_ifma,
    };
    assert!(
        digest.len() == hash.digest_len()
            && signature.len() == key.n.len()
            && scratch.len() == public_scratch_words(key.n.len())
    );
    let pre = key.pre(scratch);
    // SAFETY: each pointer is valid for its length (`scratch` for writes),
    // and none overlaps another or wraps around, as they are distinct Rust
    // allocations; `PublicKey::new` gives `64 ≤ n_len ≤ 1024` and
    // `1 ≤ e_len ≤ 5 ≤ n_len`; `sig_len = n_len`, `digest_len` is the length
    // of `hash`'s values and `scratch_len = 8 ⌈n_len / 8⌉ + 1072`; `pre`
    // holds the verified precomputed values for `key.n`, with their required
    // length; `hash` and `mgf1_hash` are the numbers of MD5, SHA-1 or SHA-2
    // functions, and `h.fns` and `g.fns` their streaming functions, for
    // implementations the CPU can run (`table`); and the CPU has the
    // features of `f`, which `select` chose.
    unsafe {
        f(
            key.n.as_ptr(),
            key.n.len(),
            key.e.as_ptr(),
            key.e.len(),
            digest.as_ptr(),
            digest.len(),
            signature.as_ptr(),
            signature.len(),
            any,
            salt_len,
            scratch.as_mut_ptr(),
            scratch.len(),
            pre.as_ptr(),
            pre.len(),
            h.id,
            g.id,
            &h.fns,
            &g.fns,
        )
    }
}
