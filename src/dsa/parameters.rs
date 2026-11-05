//! DSA parameter generation, for the three FIPS 186-4 generation sizes.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]

// Hashing, primality tests, retries, generator selection and the final
// validation are all verified code. On x86-64 and i686 the Rust refills one tape
// as the search asks (`search`); elsewhere it supplies the three entropy tapes. It
// allocates the output and working space, and chooses the implementation.

#[cfg(not(any(target_arch = "x86_64", target_arch = "x86")))]
use alloc::vec;
use alloc::vec::Vec;

use super::{Error, Secret};
#[cfg(not(any(target_arch = "x86_64", target_arch = "x86")))]
use crate::arch::dsa::vg_dsa_generate_parameters;
#[cfg(target_arch = "aarch64")]
use crate::arch::dsa::{
    vg_dsa_generate_parameters_sha1_sha2, vg_dsa_generate_parameters_sha1_sha2_sha256_sha2,
    vg_dsa_generate_parameters_sha256_sha2,
};
#[cfg(not(any(target_arch = "x86_64", target_arch = "x86")))]
use crate::cpu::detected;
#[cfg(not(any(target_arch = "x86_64", target_arch = "x86")))]
use verified_garbage_cpu::Features;

mod search;

/// Generated probable-prime DSA domain parameters, encoded big-endian.
#[derive(Clone, Debug)]
pub struct Parameters {
    packed: Vec<u8>,
    p_len: usize,
    q_len: usize,
}

impl Parameters {
    /// Generate a domain with a 1024-, 2048-, or 3072-bit modulus using the
    /// operating system's random number generator. The subgroup has 160 bits
    /// for a 1024-bit modulus and 256 bits otherwise.
    ///
    /// The complete search runs in verified assembly over bounded entropy
    /// tapes. Exhaustion returns [`Error::InvalidKeyOrNonce`]. Primality uses
    /// trial division and independent Miller–Rabin witnesses; this produces
    /// probable primes, rather than primality certificates. The generation
    /// contract treats the entropy tapes as public: search timing can depend
    /// on their contents. These are domain parameters shared between keys.
    pub fn generate(bits: usize) -> Result<Self, Error> {
        Self::generate_from(bits, |buf| {
            getrandom::fill(buf).map_err(|_| Error::Randomness)
        })
    }

    /// [`generate`](Self::generate), with its entropy tapes filled by
    /// `random` instead of the operating system.
    ///
    /// Not part of the API: it lets benchmarks compare implementations on
    /// identical work, from fixed tapes. The result is generated as FIPS
    /// 186-4 requires only if `random` supplies uniformly random bytes.
    #[cfg(feature = "internal-bench")]
    #[doc(hidden)]
    pub fn generate_with_rng(
        bits: usize,
        random: impl FnMut(&mut [u8]) -> Result<(), Error>,
    ) -> Result<Self, Error> {
        Self::generate_from(bits, random)
    }

    /// [`generate`](Self::generate), with its entropy tapes filled by
    /// `random`.
    fn generate_from(
        bits: usize,
        random: impl FnMut(&mut [u8]) -> Result<(), Error>,
    ) -> Result<Self, Error> {
        let (p_len, q_len) = match bits {
            1024 => (128, 20),
            2048 => (256, 32),
            3072 => (384, 32),
            _ => return Err(Error::Length),
        };
        #[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
        let packed = search::generate(p_len, q_len, random)?;
        #[cfg(not(any(target_arch = "x86_64", target_arch = "x86")))]
        let packed = tapes(p_len, q_len, random)?;
        Ok(Self {
            packed,
            p_len,
            q_len,
        })
    }

    /// The fixed-width big-endian prime modulus.
    pub fn p(&self) -> &[u8] {
        &self.packed[..self.p_len]
    }

    /// The fixed-width big-endian subgroup order.
    pub fn q(&self) -> &[u8] {
        &self.packed[self.p_len..self.p_len + self.q_len]
    }

    /// The fixed-width big-endian subgroup generator.
    pub fn g(&self) -> &[u8] {
        &self.packed[self.p_len + self.q_len..]
    }
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "x86")))]
type Generate = unsafe extern "C" fn(
    *mut u8,
    usize,
    usize,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *mut u64,
    usize,
) -> u32;

/// The finite search over three fixed tapes (`VG.Spec.Dsa.generateParametersBytes`),
/// on the targets that do not have the refillable-tape search yet.
#[cfg(not(any(target_arch = "x86_64", target_arch = "x86")))]
fn tapes(
    p_len: usize,
    q_len: usize,
    mut random: impl FnMut(&mut [u8]) -> Result<(), Error>,
) -> Result<Vec<u8>, Error> {
    let mut seeds = Secret(vec![0; 4096 * q_len]);
    let mut hs = Secret(vec![0; 128 * p_len]);
    let mut witnesses = Secret(vec![0; 16384 * p_len]);
    random(&mut seeds.0)?;
    random(&mut hs.0)?;
    random(&mut witnesses.0)?;
    let mut packed = vec![0; 2 * p_len + q_len];
    let mut scratch = Secret(vec![0u64; 64 * p_len + 1024]);
    let generate = select(detected());
    // SAFETY: the size match establishes the three supported widths.
    // Seed and h tapes contain whole chunks, output has 2*p_len+q_len
    // bytes, and scratch has 64*p_len+1024 words. Every buffer is a
    // distinct owned allocation. Selection checks all CPU features.
    let status = unsafe {
        generate(
            packed.as_mut_ptr(),
            packed.len(),
            p_len,
            q_len,
            seeds.0.as_ptr(),
            seeds.0.len(),
            hs.0.as_ptr(),
            hs.0.len(),
            witnesses.0.as_ptr(),
            witnesses.0.len(),
            scratch.0.as_mut_ptr(),
            scratch.0.len(),
        )
    };
    if status != 1 {
        return Err(Error::InvalidKeyOrNonce);
    }
    Ok(packed)
}

#[cfg(test)]
mod tests;

#[cfg(target_arch = "aarch64")]
fn select(features: Features) -> Generate {
    use crate::hashes::{sha1::Sha1Backend, sha256::Sha256Backend};
    select_backends(
        Sha1Backend::select(features),
        Sha256Backend::select(features),
    )
}

#[cfg(target_arch = "aarch64")]
fn select_backends(
    sha1: crate::hashes::sha1::Sha1Backend,
    sha256: crate::hashes::sha256::Sha256Backend,
) -> Generate {
    use crate::hashes::{sha1::Sha1Backend as H1, sha256::Sha256Backend as H256};
    match (sha1, sha256) {
        (H1::Scalar, H256::Scalar) => vg_dsa_generate_parameters,
        (H1::Scalar, H256::Sha2) => vg_dsa_generate_parameters_sha256_sha2,
        (H1::Sha2, H256::Scalar) => vg_dsa_generate_parameters_sha1_sha2,
        (H1::Sha2, H256::Sha2) => vg_dsa_generate_parameters_sha1_sha2_sha256_sha2,
    }
}

/// The PPC64LE implementation: neither hash has a variant there, so the
/// match names only their baselines, and a new hash backend does not compile
/// until generation handles it.
#[cfg(target_arch = "powerpc64")]
fn select(features: Features) -> Generate {
    use crate::hashes::{sha1::Sha1Backend as H1, sha256::Sha256Backend as H256};
    match (H1::select(features), H256::select(features)) {
        (H1::Scalar, H256::Scalar) => vg_dsa_generate_parameters,
    }
}

/// The ARMv7 implementations: `vg_dsa_generate_parameters_umaal` where the
/// operating system runs on A-profile cores alone, on CPUs with the features
/// its `_FEATURES` constant names, else the baseline.
#[cfg(all(
    target_arch = "arm",
    any(
        target_os = "linux",
        target_os = "android",
        target_os = "freebsd",
        target_os = "netbsd",
        target_os = "openbsd"
    )
))]
fn select(features: Features) -> Generate {
    use crate::arch::dsa::VG_DSA_GENERATE_PARAMETERS_UMAAL_FEATURES;
    select_backends(features.contains(VG_DSA_GENERATE_PARAMETERS_UMAAL_FEATURES))
}

#[cfg(all(
    target_arch = "arm",
    any(
        target_os = "linux",
        target_os = "android",
        target_os = "freebsd",
        target_os = "netbsd",
        target_os = "openbsd"
    )
))]
fn select_backends(umaal: bool) -> Generate {
    use crate::arch::dsa::vg_dsa_generate_parameters_umaal;
    match umaal {
        false => vg_dsa_generate_parameters,
        true => vg_dsa_generate_parameters_umaal,
    }
}

#[cfg(all(
    target_arch = "arm",
    not(any(
        target_os = "linux",
        target_os = "android",
        target_os = "freebsd",
        target_os = "netbsd",
        target_os = "openbsd"
    ))
))]
fn select(_features: Features) -> Generate {
    vg_dsa_generate_parameters
}
