//! DSA composition over verified Montgomery and selection primitives.
//! All loops over private values have public bounds. Rust composition is not
//! covered by the complete DSA contracts of the x86-64 implementation.
use super::{Secret, nonce_in_range};
use crate::arch::ffdh::vg_ffdh_choose;
use crate::ct;
use crate::ffdh::arithmetic::{Montgomery, bits, divides, minus_one, value_cmp};
use alloc::vec;
use core::cmp::Ordering;

struct Domain<'a> {
    q: &'a [u8],
    g: &'a [u8],
    y: &'a [u8],
    p_mont: Montgomery,
    q_mont: Montgomery,
}

impl<'a> Domain<'a> {
    fn new(key: &'a [u8], p_len: usize, q_len: usize) -> Option<Self> {
        let (p, rest) = key.split_at(p_len);
        let (q, rest) = rest.split_at(q_len);
        let (g, rest) = rest.split_at(p_len);
        let y = &rest[..p_len];
        if !matches!(
            (bits(p), bits(q)),
            (1024, 160) | (2048, 224 | 256) | (3072, 256)
        ) || p[p.len() - 1] & 1 == 0
            || q[q.len() - 1] & 1 == 0
            || !divides(q, &minus_one(p))
            || value_cmp(g, &[1]) != Ordering::Greater
            || value_cmp(g, p) != Ordering::Less
            || value_cmp(y, &[1]) != Ordering::Greater
            || value_cmp(y, p) != Ordering::Less
        {
            return None;
        }
        let p_mont = Montgomery::new(p);
        if value_cmp(&p_mont.power_public(g, q), &[1]) != Ordering::Equal
            || value_cmp(&p_mont.power_public(y, q), &[1]) != Ordering::Equal
        {
            return None;
        }
        Some(Self {
            q,
            g,
            y,
            p_mont,
            q_mont: Montgomery::new(q),
        })
    }

    fn inverse(&self, a: &[u8]) -> Secret<u8> {
        // q is public and odd. Subtraction may borrow across a trailing 0x01.
        let mut exponent = self.q.to_vec();
        let mut borrow = 2u16;
        for byte in exponent.iter_mut().rev() {
            let difference = u16::from(*byte).wrapping_sub(borrow);
            *byte = difference as u8;
            borrow = difference >> 15;
        }
        Secret(self.q_mont.power(a, &exponent))
    }

    fn digest(&self, digest: &[u8]) -> Secret<u8> {
        // Supported subgroup bit lengths are byte-aligned. Truncate before
        // reduction, preserving the value of digests shorter than N bits.
        reduce(&digest[..digest.len().min(bits(self.q) / 8)], self.q)
    }
}

/// Fixed-schedule long reduction. An extra byte holds the shift carry.
/// Selection crosses the opaque verified assembly boundary, so Rust cannot
/// turn a secret comparison into a conditional copy or indexed table load.
fn reduce(input: &[u8], modulus: &[u8]) -> Secret<u8> {
    let n = modulus.len();
    let mut rem = Secret(vec![0u8; n + 1]);
    let mut difference = Secret(vec![0u8; n + 1]);
    for &byte in input {
        for bit in (0..8).rev() {
            let mut carry = (byte >> bit) & 1;
            for v in rem.0.iter_mut().rev() {
                let next = *v >> 7;
                *v = (*v << 1) | carry;
                carry = next;
            }
            let mut borrow = 0u16;
            for i in (0..=n).rev() {
                let m = if i == 0 { 0 } else { modulus[i - 1] };
                let d = u16::from(rem.0[i]).wrapping_sub(u16::from(m) + borrow);
                difference.0[i] = d as u8;
                borrow = d >> 15;
            }
            // SAFETY: choose accepts arbitrary values and selects by bit 0.
            let mask = unsafe { vg_ffdh_choose(0, u64::MAX, u64::from(borrow ^ 1)) } as u8;
            for (v, &d) in rem.0.iter_mut().zip(&difference.0) {
                *v = (*v & !mask) | (d & mask);
            }
        }
    }
    Secret(rem.0[1..].to_vec())
}

fn add(a: &[u8], b: &[u8], modulus: &[u8]) -> Secret<u8> {
    let mut sum = Secret(vec![0; modulus.len() + 1]);
    let mut carry = 0u16;
    for i in (0..modulus.len()).rev() {
        carry += u16::from(a[i]) + u16::from(b[i]);
        sum.0[i + 1] = carry as u8;
        carry >>= 8;
    }
    sum.0[0] = carry as u8;
    reduce(&sum.0, modulus)
}

pub(super) fn sign(
    key: &[u8],
    p_len: usize,
    q_len: usize,
    digest: &[u8],
    nonce: &[u8],
    output: &mut [u8],
) -> bool {
    output.fill(0);
    let Some(domain) = Domain::new(key, p_len, q_len) else {
        return false;
    };
    let x = &key[3 * p_len + q_len..];
    let public = Secret(domain.p_mont.power(domain.g, x));
    let valid =
        nonce_in_range(x, domain.q) & nonce_in_range(nonce, domain.q) & ct::eq(&public.0, domain.y);
    let power = Secret(domain.p_mont.power(domain.g, nonce));
    let r = reduce(&power.0, domain.q);
    let xr = Secret(domain.q_mont.product(x, &r.0));
    let z = domain.digest(digest);
    let sum = add(&z.0, &xr.0, domain.q);
    let inverse = domain.inverse(nonce);
    let s = Secret(domain.q_mont.product(&inverse.0, &sum.0));
    let zero = vec![0; q_len];
    if !(valid & !ct::eq(&r.0, &zero) & !ct::eq(&s.0, &zero)) {
        return false;
    }
    output[..q_len].copy_from_slice(&r.0);
    output[q_len..].copy_from_slice(&s.0);
    true
}

pub(super) fn verify(
    key: &[u8],
    p_len: usize,
    q_len: usize,
    digest: &[u8],
    signature: &[u8],
) -> bool {
    let Some(domain) = Domain::new(key, p_len, q_len) else {
        return false;
    };
    let (r, s) = signature.split_at(q_len);
    if !nonce_in_range(r, domain.q) || !nonce_in_range(s, domain.q) {
        return false;
    }
    let inverse = domain.inverse(s);
    let z = domain.digest(digest);
    let u1 = Secret(domain.q_mont.product(&z.0, &inverse.0));
    let u2 = Secret(domain.q_mont.product(r, &inverse.0));
    let a = Secret(domain.p_mont.power(domain.g, &u1.0));
    let b = Secret(domain.p_mont.power(domain.y, &u2.0));
    let ab = Secret(domain.p_mont.product(&a.0, &b.0));
    let v = reduce(&ab.0, domain.q);
    ct::eq(&v.0, r)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reduction_addition_and_products_match_integer_arithmetic() {
        // Independent integer oracles exercise zero, carry, equality, and
        // non-byte-aligned moduli, including leading-zero encodings.
        for modulus in [3u64, 5, 127, 129, 255, 257, 65535, 65537] {
            for width in [3, 8] {
                let m = &modulus.to_be_bytes()[8 - width..];
                let mont = Montgomery::new(m);
                for a in [0, 1, modulus - 1, modulus, modulus + 1, u32::MAX as u64] {
                    let reduced = reduce(&a.to_be_bytes(), m);
                    assert_eq!(reduced.0, (a % modulus).to_be_bytes()[8 - width..]);
                    for b in [0, 1, modulus - 1] {
                        let bytes = b.to_be_bytes();
                        let b = &bytes[8 - width..];
                        let sum = add(&reduced.0, b, m);
                        let b_value = u64::from_be_bytes(bytes);
                        assert_eq!(
                            sum.0,
                            ((a % modulus + b_value) % modulus).to_be_bytes()[8 - width..]
                        );
                        assert_eq!(
                            mont.product(&reduced.0, b),
                            ((a % modulus * b_value) % modulus).to_be_bytes()[8 - width..]
                        );
                    }
                }
            }
        }
    }
}
