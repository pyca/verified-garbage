//! Public arithmetic for parameter generation.
#[cfg(target_arch = "x86_64")]
use crate::arch::ffdh::{
    VG_FFDH_CHECK_DOMAIN_ADX_FEATURES, VG_FFDH_CHECK_PRIVATE_ADX_FEATURES,
    VG_FFDH_CHECK_PUBLIC_ADX_FEATURES, VG_FFDH_EXCHANGE_ADX_FEATURES,
    VG_FFDH_GENERATE_KEY_ADX_FEATURES,
};
use crate::arch::miller_rabin::vg_miller_rabin_round;
#[cfg(target_arch = "x86_64")]
use crate::arch::miller_rabin::{VG_MILLER_RABIN_ROUND_ADX_FEATURES, vg_miller_rabin_round_adx};
use crate::arch::rsa_mont::vg_rsa_mont_mul;
#[cfg(target_arch = "x86_64")]
use crate::arch::rsa_mont::{VG_RSA_MONT_MUL_ADX_FEATURES, vg_rsa_mont_mul_adx};
use crate::cpu::{Features, detected};
use crate::rsa::Scratch;
use alloc::{vec, vec::Vec};
use core::cmp::Ordering;

pub(super) fn canonical(a: &[u8]) -> &[u8] {
    &a[a.iter().position(|&b| b != 0).unwrap_or(a.len())..]
}
pub(super) fn bits(a: &[u8]) -> usize {
    let a = canonical(a);
    a.first()
        .map_or(0, |b| 8 * a.len() - b.leading_zeros() as usize)
}
pub(super) fn value_cmp(a: &[u8], b: &[u8]) -> Ordering {
    let (a, b) = (canonical(a), canonical(b));
    a.len().cmp(&b.len()).then_with(|| a.cmp(b))
}
pub(super) fn scalar(a: &[u8], len: usize) -> Vec<u8> {
    let a = canonical(a);
    let mut out = vec![0; len];
    out[len - a.len()..].copy_from_slice(a);
    out
}
/// Subtract one from a public odd modulus, so there is no borrow.
pub(super) fn minus_one(a: &[u8]) -> Vec<u8> {
    let mut out = a.to_vec();
    let last = out.len() - 1;
    out[last] -= 1;
    out
}

/// The implementations of the verified functions FFDH calls: the baseline
/// ISA's, or on x86-64 their `_adx` variants. Each use selects it from the
/// features of the functions it calls; RSA's private-key routines have
/// additional feature requirements that do not apply to these functions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Backend {
    Baseline,
    #[cfg(target_arch = "x86_64")]
    Adx,
}
impl Backend {
    /// The implementation of the FFDH operations (`vg_ffdh_*`, in
    /// `Domain`) a CPU with the features `_f` can run.
    pub(super) fn ffdh(_f: Features) -> Self {
        #[cfg(target_arch = "x86_64")]
        if _f.contains(
            const {
                Features::all(&[
                    VG_FFDH_CHECK_DOMAIN_ADX_FEATURES,
                    VG_FFDH_CHECK_PUBLIC_ADX_FEATURES,
                    VG_FFDH_CHECK_PRIVATE_ADX_FEATURES,
                    VG_FFDH_GENERATE_KEY_ADX_FEATURES,
                    VG_FFDH_EXCHANGE_ADX_FEATURES,
                ])
            },
        ) {
            return Self::Adx;
        }
        Self::Baseline
    }

    /// The implementation of `Montgomery`'s multiplication and
    /// Miller–Rabin round a CPU with the features `_f` can run.
    pub(super) fn montgomery(_f: Features) -> Self {
        #[cfg(target_arch = "x86_64")]
        if _f.contains(
            const {
                Features::all(&[
                    VG_RSA_MONT_MUL_ADX_FEATURES,
                    VG_MILLER_RABIN_ROUND_ADX_FEATURES,
                ])
            },
        ) {
            return Self::Adx;
        }
        Self::Baseline
    }
}

#[derive(Clone, Debug)]
pub(super) struct Montgomery {
    modulus: Vec<u64>,
    r2: Vec<u64>,
    minv: u64,
    backend: Backend,
}
impl Montgomery {
    /// Only public values are used in precomputation. Works for any odd
    /// modulus >=3, including the 511-bit Sophie Germain prime of a 512-bit p.
    pub(super) fn new(p: &[u8]) -> Self {
        let w = p.len().div_ceil(8).max(4);
        let modulus = words(p, w);
        let mut inv = 1u64;
        for _ in 0..6 {
            inv = inv.wrapping_mul(2u64.wrapping_sub(modulus[0].wrapping_mul(inv)));
        }
        let mut r2 = vec![0u64; w];
        r2[0] = 1;
        for _ in 0..128 * w {
            double_mod(&mut r2, &modulus);
        }
        Self {
            modulus,
            r2,
            minv: inv.wrapping_neg(),
            backend: Backend::montgomery(detected()),
        }
    }
    /// One strong probable-prime witness, using the shared verified RSA round.
    /// `s` is the number of trailing zero bits of the public candidate minus one.
    pub(super) fn strong_probable_prime(&self, base: &[u8], s: usize) -> bool {
        let w = self.modulus.len();
        let at = |j| 32 + j * (w + 2);
        let mut ws = self.workspace(base);
        #[cfg(target_arch = "x86_64")]
        let (exponent, one, minus_one) = (24, 25, 26);
        #[cfg(target_arch = "aarch64")]
        let (exponent, one, minus_one) = (27, 9, 10);
        ws.copy_within(at(5)..at(5) + w, at(one));
        ws.copy_within(at(4)..at(4) + w, at(5));
        let mut borrow = false;
        for i in 0..w {
            let (value, b1) = self.modulus[i].overflowing_sub(ws[at(one) + i]);
            let (value, b2) = value.overflowing_sub(u64::from(borrow));
            ws[at(minus_one) + i] = value;
            borrow = b1 | b2;
        }
        // Shift only 1..=4 bits: the window proof handles the remaining
        // trailing zero bits. Its final window mask also needs s modulo 64.
        let shift = 1 + (s - 1) % 4;
        for i in 0..w {
            let low = self.modulus[i] - u64::from(i == 0);
            let high = self.modulus.get(i + 1).copied().unwrap_or(0);
            ws[at(exponent) + i] = (low >> shift) | (high << (64 - shift));
        }
        ws[at(exponent) + w] = 1 << (s % 64);
        #[cfg(target_arch = "aarch64")]
        {
            ws[28] = (8 * (w + 2)) as u64;
        }
        let round = match self.backend {
            Backend::Baseline => vg_miller_rabin_round,
            #[cfg(target_arch = "x86_64")]
            Backend::Adx => vg_miller_rabin_round_adx,
        };
        // SAFETY: w is 4..=128, the odd modulus is at least 3, and the
        // stable allocation contains 28 arrays of w+2 words. The Montgomery
        // header and witness are initialized by workspace; one and minus
        // one are their canonical Montgomery residues. The exponent and
        // extra word have the shared prepared-round contract's values.
        // The allocation is disjoint from the stack and wiped on drop.
        // The ADX backend is selected only with the round's generated
        // feature set.
        unsafe { round(ws.as_mut_ptr(), ws.len()) == 1 }
    }

    fn workspace(&self, base: &[u8]) -> Scratch {
        let w = self.modulus.len();
        let mut ws = Scratch::new(32 + 28 * (w + 2));
        ws[6] = w as u64;
        ws[7] = self.minv;
        for j in 0..8 {
            // SAFETY: each array starts inside this stable allocation.
            ws[8 + j] = unsafe { ws.as_ptr().add(32 + j * (w + 2)) } as u64;
        }
        let at = |j| 32 + j * (w + 2);
        ws[at(0)..at(0) + w].copy_from_slice(&self.modulus);
        ws[at(1)..at(1) + w].copy_from_slice(&self.r2);
        ws[at(4)..at(4) + w].copy_from_slice(&words(base, w));
        ws[at(7)] = 1;
        self.mul(&mut ws, 4, 4, 1);
        self.mul(&mut ws, 5, 7, 1);
        ws
    }

    fn mul(&self, ws: &mut [u64], out: u32, a: u32, b: u32) {
        let f = match self.backend {
            Backend::Baseline => vg_rsa_mont_mul,
            #[cfg(target_arch = "x86_64")]
            Backend::Adx => vg_rsa_mont_mul_adx,
        };
        // SAFETY: ws has at least 32+8*(w+2) words, w>=2 and w<=128. The header
        // points into this allocation, stores the odd modulus' negative
        // inverse and w, and indices are among 1,4,5,6,7. Each b is below
        // the modulus: R², one, or a prior Montgomery result. Scratch owns
        // the writable allocation, outside the callee's stack; it is wiped
        // on drop. ADX is selected only with the multiplication's generated
        // feature set.
        unsafe { f(ws.as_mut_ptr(), ws.len(), out, a, b) }
    }
}
fn words(a: &[u8], w: usize) -> Vec<u64> {
    let mut out = vec![0; w];
    for (i, &b) in a.iter().rev().enumerate() {
        out[i / 8] |= u64::from(b) << (8 * (i % 8));
    }
    out
}
/// Public modular doubling, retaining the high carry until subtraction.
fn double_mod(a: &mut [u64], m: &[u64]) {
    let mut carry = 0;
    for v in a.iter_mut() {
        let next = *v >> 63;
        *v = (*v << 1) | carry;
        carry = next;
    }
    if carry != 0 || a.iter().rev().cmp(m.iter().rev()).is_ge() {
        let mut borrow = false;
        for (v, &modulus) in a.iter_mut().zip(m) {
            let (x, b1) = v.overflowing_sub(modulus);
            let (x, b2) = x.overflowing_sub(u64::from(borrow));
            *v = x;
            borrow = b1 | b2;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strong_witness_matches_integer_arithmetic() {
        // An independent small-integer oracle exercises early acceptance,
        // rejection, and repeated squares, including nontrivial roots of one.
        for p in (3u64..1024).step_by(2) {
            let s = (p - 1).trailing_zeros() as usize;
            let d = (p - 1) >> s;
            let mont = Montgomery::new(&p.to_be_bytes());
            for a in [2, p / 2, p - 2] {
                let mut expected = 1;
                for _ in 0..d {
                    expected = expected * a % p;
                }
                let mut passes = expected == 1 || expected == p - 1;
                for _ in 1..s {
                    expected = expected * expected % p;
                    passes |= expected == p - 1;
                }
                assert_eq!(mont.strong_probable_prime(&a.to_be_bytes(), s), passes);
            }
        }
    }

    #[test]
    fn strong_witness_matches_power_of_two_moduli() {
        // Construct 2^k+1 arithmetically. Its odd exponent is one, and its
        // two-adic valuation exercises the shifted exponent's extra word.
        for k in [63, 64, 65, 127, 255, 511, 8191] {
            let mut p = vec![0; (k + 1_usize).div_ceil(8)];
            p[0] = 1 << (k % 8);
            let last = p.len() - 1;
            p[last] |= 1;
            let mont = Montgomery::new(&p);
            // The order of 2 modulo 2^k+1 is exactly 2k. A repeated
            // squaring reaches -1 precisely when k is a power of two.
            assert_eq!(mont.strong_probable_prime(&[2], k), k.is_power_of_two());
        }
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn backend_feature_requirements() {
        // Both selections need exactly BMI2 and ADX, the generated feature
        // sets of the functions they call. AVX, AVX2 and IFMA belong to
        // other RSA routines: they neither enable ADX nor gate it when BMI2
        // and ADX are present.
        let cases: &[(&[&str], Backend)] = &[
            (&[], Backend::Baseline),
            (&["bmi2"], Backend::Baseline),
            (&["adx"], Backend::Baseline),
            (&["avx", "avx2"], Backend::Baseline),
            (&["avx", "avx2", "bmi2"], Backend::Baseline),
            (&["avx", "avx2", "adx"], Backend::Baseline),
            (
                &["avx", "avx2", "avx512f", "avx512ifma", "avx512vl"],
                Backend::Baseline,
            ),
            (&["bmi2", "adx"], Backend::Adx),
            (&["avx", "avx2", "bmi2", "adx"], Backend::Adx),
            (
                &[
                    "avx",
                    "avx2",
                    "avx512f",
                    "bmi2",
                    "adx",
                    "avx512ifma",
                    "avx512vl",
                ],
                Backend::Adx,
            ),
        ];
        for &(features, expected) in cases {
            for select in [Backend::ffdh, Backend::montgomery] {
                assert_eq!(select(Features::of(features)), expected, "{features:?}");
            }
        }
    }
}
