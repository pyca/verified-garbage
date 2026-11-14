//! DSA parameter generation, for the three FIPS 186-4 generation sizes.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

// Hashing, primality tests, retries, generator selection and the final
// validation are all verified code. The Rust refills the search's one tape as
// it asks (`search`), allocates the output and working space, and chooses the
// implementation.

use alloc::vec::Vec;

use super::{Error, Secret};

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
    /// The complete search runs in verified assembly over a bounded entropy
    /// tape, refilled as it asks. Exhaustion returns [`Error::InvalidKeyOrNonce`]. Primality uses
    /// trial division and independent Miller–Rabin witnesses; this produces
    /// probable primes, rather than primality certificates. The generation
    /// contract treats the entropy tape as public: search timing can depend
    /// on its contents. These are domain parameters shared between keys.
    pub fn generate(bits: usize) -> Result<Self, Error> {
        Self::generate_from(bits, |buf| {
            getrandom::fill(buf).map_err(|_| Error::Randomness)
        })
    }

    /// [`generate`](Self::generate), with its entropy tape filled by
    /// `random` instead of the operating system.
    ///
    /// Not part of the API: it lets benchmarks compare implementations on
    /// identical work, from a fixed tape. The result is generated as FIPS
    /// 186-4 requires only if `random` supplies uniformly random bytes.
    #[cfg(feature = "internal-bench")]
    #[doc(hidden)]
    pub fn generate_with_rng(
        bits: usize,
        random: impl FnMut(&mut [u8]) -> Result<(), Error>,
    ) -> Result<Self, Error> {
        Self::generate_from(bits, random)
    }

    /// [`generate`](Self::generate), with its entropy tape filled by
    /// `random`.
    fn generate_from(
        bits: usize,
        random: impl FnMut(&mut [u8]) -> Result<(), Error>,
    ) -> Result<Self, Error> {
        crate::dit::enter!(dit);
        let (p_len, q_len) = match bits {
            1024 => (128, 20),
            2048 => (256, 32),
            3072 => (384, 32),
            _ => return Err(Error::Length),
        };
        let packed = search::generate(dit, p_len, q_len, random)?;
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

#[cfg(test)]
mod tests;
