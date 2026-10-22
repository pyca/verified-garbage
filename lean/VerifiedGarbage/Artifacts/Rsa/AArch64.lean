module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareHelper
public import VerifiedGarbage.Proof.Rsa.AArch64.FoldedChecked
public import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBase
public import VerifiedGarbage.Proof.Rsa.AArch64.CvVerified
public import VerifiedGarbage.Proof.Rsa.AArch64.CkVerified
public import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyVerified
public import VerifiedGarbage.Proof.Rsa.AArch64.RpVerified
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSA (RFC 8017) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Rsa.AArch64

/-- The two repeated squares are shared by all RSA callers. -/
def squareHelper (slot : Spec.Rsa.MontSquare.Slot) : Artifact :=
  let M := match slot with
    | .r2 => Proof.Bignum.AArch64.Mont.blocked
    | .y => Proof.Bignum.AArch64.Mont.squareEight
  (Spec.Rsa.MontSquare.squareApi slot).artifact AArch64.target {
    notes := ["Baseline AArch64 symmetric square with eight-limb blocked reduction for widths \
        of at least sixteen limbs divisible by eight; other widths retain the row-wise reduction."]
    code := M.mm slot.index slot.index slot.index
    verified := Proof.Bignum.AArch64.SquareHelper.verified M slot }

/-- Share the repeated five-square window body across all CRT callers. -/
def windowHelper : Artifact :=
  Spec.Rsa.MontWindow.windowApi.artifact AArch64.target {
    notes := ["Baseline AArch64: shares register saves across five lazy Montgomery squares and one \
        canonical product, with a constant-time four-vector table scan. Widths of at least sixteen \
        limbs divisible by eight use eight-limb product tiles and blocked reduction; other widths \
        retain the existing canonical square and multiplication kernels."]
    code := Proof.Bignum.AArch64.WindowFive.body.code
    verified := Proof.Bignum.AArch64.WindowShared.verified }

def artifacts : List Artifact := [squareHelper .r2, squareHelper .y, windowHelper,
  Spec.Rsa.publicPrecomputeApi.artifact AArch64.target {
    notes := ["Baseline AArch64: R² mod n, for n of `w` words whose top bit is set (every modulus of a \
        whole number of words), by `w` word steps of long division from `R - n`, each step's quotient \
        estimated from the top words with a reciprocal of n's top word, and n added back only while the \
        remainder is negative, by a branch on values of n alone; for other n, from `2^(b - 1)`, for n \
        of `b` bits, by doublings to `2^w R mod n`, then six Montgomery squarings."]
    code := Impl.Rsa.AArch64.Precompute.code Proof.Bignum.AArch64.Mont.base.mm
    verified := Proof.Bignum.AArch64.precompute_verified _ },
  Spec.Rsa.publicPrecomputedCheckedApi.artifact AArch64.target {
    notes := ["Baseline AArch64: `e` is checked first, its bytes read into a register saturated at \
        `2^34 - 1` once they reach `2^33`; then Montgomery multiplication. The exponent 65537 (three \
        bytes) uses sixteen squares and a final multiplication by the ordinary input that also \
        converts out of Montgomery form; other exponents are scanned left to right from their first \
        set bit, which starts the result as the input, a square per later bit and a multiplication \
        per later set bit. `pre` is checked (`n` odd, its top word not zero, `R² mod n` below it) \
        before any arithmetic, so that values of no modulus are safe."]
    code := Impl.Rsa.AArch64.Folded.checked Proof.Bignum.AArch64.Mont.productEight.mm
    verified := Proof.Rsa.AArch64.FoldedPublic.checked_verified _ },
  Spec.Rsa.privateCrtApi.artifact AArch64.target {
    notes := ["Baseline AArch64: the checks (`n` as `vg_rsa_public_precompute` checks it, the input \
        below `n`, `p q = n` by a product of the two, `qInv < p`) give a mask; the primes are \
        replaced by 3 under a clear mask, so that the arithmetic is the same whatever the key, and \
        the result is stored masked. Each prime has its own working space, with its own \
        Montgomery multiplication; the input is reduced modulo it by \
        Montgomery reduction of chunks of its size, and the exponents are scanned left to right \
        over all their bits. Moduli of at least 128 bytes whose two prime byte lengths are \
        multiples of 64 use shared five-bit windows, 32-entry tables within the existing scratch \
        allocation, and a four-vector masked scan. Other lengths retain the four-bit window. The final partial window consumes exactly its remaining bits."]
    code := Proof.Bignum.AArch64.WindowFive.code
    verified := Proof.Bignum.AArch64.WindowFive.base_verified },
  Spec.Rsa.crtValuesApi.artifact AArch64.target {
    notes := ["Baseline AArch64: `n` is checked as `vg_rsa_public_precompute` checks it; then the \
        checks (`p q = n`, as `n mod p = 0`, `n / p = q` and `p` odd, and `gcd(q, p) = 1`) give a \
        mask, the arithmetic is the same whatever the key, and the results are stored masked. The \
        remainders and quotients are computed by bit-serial division, `64 w` steps for `w`-word \
        numbers, and `qInv` by `128 w` steps of the binary extended Euclidean algorithm modulo `p`, \
        each step's swaps and subtractions under masks."]
    code := Impl.Rsa.AArch64.Keys.CrtValues.code
    verified := Proof.Rsa.AArch64.cv_verified },
  Spec.Rsa.recoverPrimesApi.artifact AArch64.target {
    notes := ["Baseline AArch64: `n` is checked as `vg_rsa_public_precompute` checks it; `d e` and \
        the halvings of `d e - 1` (`r` odd and `t` its twos) run over `64 Bw` steps for `Bw` words \
        of `d e`, whatever their values. Each candidate `g` computes `g^r mod n` by \
        Montgomery multiplication over all the bits of `r`, a square and a multiplication by `g` or \
        1 (a masked selection) per bit, then `64 Bw` squarings, each kept or not under masks; the \
        candidates stop at the first that finds the factors, which is the only branch on the key. \
        `gcd(y - 1, n)` is `128 w` steps of the binary extended Euclidean algorithm, and `n / p` \
        `64 w` steps of bit-serial division."]
    code := Impl.Rsa.AArch64.Recover.code Proof.Bignum.AArch64.Mont.base.mm
    verified := Proof.Rsa.AArch64.rp_verified _ },
  Spec.Rsa.checkKeyApi.artifact AArch64.target {
    notes := ["Baseline AArch64: `e` is checked as `vg_rsa_public_precomputed_checked` checks it and \
        `n` as `vg_rsa_public_precompute` checks it, which are the only branches on the key. Then every check \
        of the private key is computed whatever its outcome and and'ed into a mask, in a working space \
        of `W = 2 w + 2` words for `w`-word numbers: the comparisons by a subtraction's borrow, \
        `p q = n` by a product of the two, and each remainder (`d e mod (p - 1)` and the others, \
        `q qInv mod p`) by bounded bit-serial division with masked subtraction. The full-exponent \
        checks process `64 (⌈other_factor_len / 8⌉ + 1)` bits, using `d < n = p q`; the CRT \
        checks process 64 bits for `e dP` and `e dQ`, and `64 ⌈q_len / 8⌉` bits for `q qInv`."]
    code := Impl.Rsa.AArch64.CheckKey.code
    verified := Proof.Rsa.AArch64.ck_verified },
  Spec.Rsa.checkCrtKeyApi.artifact AArch64.target {
    notes := ["Baseline AArch64: `vg_rsa_check_key`'s code without the checks of `d`. `e` and `n` \
        are checked first, which are the only branches on the key; then every check of the private key is \
        computed whatever its outcome and and'ed into a mask. Each remainder (`e dP mod (p - 1)`, \
        `e dQ mod (q - 1)`, `q qInv mod p`) is computed by bit-serial division in the layout's \
        `W = 2 w + 2` words, starting from the product's words above its low `c` (`c = 1`, or \
        `⌈q_len / 8⌉` for `q qInv`), which are below the divisor when the comparison before it holds: \
        `64 c` steps rather than `64 W`."]
    code := Impl.Rsa.AArch64.CheckCrtKey.code
    verified := Proof.Rsa.AArch64.ckc_verified }]

end VG.Artifacts.Rsa.AArch64
