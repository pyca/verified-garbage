//! RSAES-OAEP on x86-64: the verified `vg_rsa_oaep_encrypt_precomputed` and
//! `vg_rsa_oaep_decrypt` (contracts `VG.Spec.RsaOaep.encryptAnyContract` and
//! `decryptAnyContract`), which take both hash functions as tables of their
//! streaming functions (`crate::hash_fns`), for each implementation of the
//! RSA operation (`crate::rsa::Backend`).

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use super::{Error, Hash};
use crate::arch::rsa_oaep::{
    vg_rsa_oaep_decrypt, vg_rsa_oaep_decrypt_adx, vg_rsa_oaep_decrypt_ifma,
    vg_rsa_oaep_encrypt_precomputed, vg_rsa_oaep_encrypt_precomputed_adx,
    vg_rsa_oaep_encrypt_precomputed_ifma,
};
use crate::cpu::detected;
use crate::hash_fns::{Table, table};
use crate::rsa::{Backend, PrivateKey, PublicKey};

/// The tables of the label's hash function `hash` and MGF1's `mgf1_hash`
/// for this CPU's implementations, or `UnsupportedHash` if either has none.
fn tables(hash: Hash, mgf1_hash: Hash) -> Result<(Table, Table), Error> {
    let f = detected();
    match (table(hash, f), table(mgf1_hash, f)) {
        (Some(h), Some(g)) => Ok((h, g)),
        _ => Err(Error::UnsupportedHash),
    }
}

/// `vg_rsa_oaep_encrypt_precomputed` for the RSA operation this CPU runs
/// best, with a random seed.
pub(super) fn encrypt(
    key: &PublicKey,
    plaintext: &[u8],
    hash: Hash,
    mgf1_hash: Hash,
    label: &[u8],
) -> Result<alloc::vec::Vec<u8>, Error> {
    let (h, g) = tables(hash, mgf1_hash)?;
    let f = match Backend::select(detected()) {
        Backend::Baseline => vg_rsa_oaep_encrypt_precomputed,
        // `select` chose them because the CPU has the features they need.
        Backend::Adx => vg_rsa_oaep_encrypt_precomputed_adx,
        Backend::Ifma => vg_rsa_oaep_encrypt_precomputed_ifma,
    };
    super::encrypt_with(
        key,
        plaintext,
        hash.digest_len(),
        |out, seed, scratch, pre| {
            // SAFETY: `encrypt_with`'s, and `seed_len` is the length of `hash`'s
            // values; `hash` and `mgf1_hash` are the numbers of SHA-1 or SHA-2
            // functions (`table` has none for others), and `h.fns` and `g.fns`
            // their streaming functions, for implementations the CPU can run
            // (`table`); the CPU has the features of `f`, which `select` chose.
            unsafe {
                f(
                    out.as_mut_ptr(),
                    out.len(),
                    key.n.as_ptr(),
                    key.n.len(),
                    key.e.as_ptr(),
                    key.e.len(),
                    label.as_ptr(),
                    label.len(),
                    plaintext.as_ptr(),
                    plaintext.len(),
                    seed.as_ptr(),
                    seed.len(),
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
        },
    )
}

/// `vg_rsa_oaep_decrypt` for the RSA operation this CPU runs best.
pub(super) fn decrypt(
    key: &PrivateKey,
    ciphertext: &[u8],
    hash: Hash,
    mgf1_hash: Hash,
    label: &[u8],
) -> Result<alloc::vec::Vec<u8>, Error> {
    let (h, g) = tables(hash, mgf1_hash)?;
    let f = match Backend::select(detected()) {
        Backend::Baseline => vg_rsa_oaep_decrypt,
        // `select` chose them because the CPU has the features they need.
        Backend::Adx => vg_rsa_oaep_decrypt_adx,
        Backend::Ifma => vg_rsa_oaep_decrypt_ifma,
    };
    super::decrypt_with(key, ciphertext, |out, len, scratch| {
        // SAFETY: `decrypt_with`'s; `hash` and `mgf1_hash` are the numbers
        // of SHA-1 or SHA-2 functions (`table` has none for others), and
        // `h.fns` and `g.fns` their streaming functions, for implementations
        // the CPU can run (`table`); the CPU has the features of `f`, which
        // `select` chose.
        unsafe {
            f(
                out.as_mut_ptr(),
                out.len(),
                len,
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
                label.as_ptr(),
                label.len(),
                ciphertext.as_ptr(),
                ciphertext.len(),
                scratch.as_mut_ptr(),
                scratch.len(),
                h.id,
                g.id,
                &h.fns,
                &g.fns,
            )
        }
    })
}
