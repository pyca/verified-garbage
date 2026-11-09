//! The non-negative integers that RSA keys are made of: see [`BigUint`].

/// A non-negative integer, as the values of an RSA key are (its modulus,
/// exponents, primes and CRT values): a view of its big-endian bytes,
/// borrowed, not copied.
#[derive(Clone, Copy)]
pub struct BigUint<'a>(&'a [u8]);

impl<'a> BigUint<'a> {
    /// The integer whose big-endian bytes are `bytes`.
    pub fn from_be_bytes(bytes: &'a [u8]) -> Self {
        BigUint(bytes)
    }

    /// The integer's big-endian bytes, as it was made from them.
    pub fn as_be_bytes(self) -> &'a [u8] {
        self.0
    }
}
