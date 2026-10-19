module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
import VerifiedGarbage.Impl.Ecdh.P384.AArch64
import VerifiedGarbage.Proof.Ecdh.AArch64.P384.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdh.AArch64.P384.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Spec.Ecdh.P384
import Mathlib.Tactic.ClearExcept

/-!
# ECDH over P-384 (SP 800-56A) on AArch64

A generic file (see `TCB/Emit.lean`) over P-384's group law and prime order `h`, the variant
`Variants/P384/AArch64/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P384.AArch64.EcdhP384

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvOrd Spec.P384.curve) : List Artifact := [
  Spec.Ecdh.P384.exchangeApi.artifact AArch64.target {
    notes := ["The function is `vg_ecdsa_p384_sign`'s \
      setup, field arithmetic and inversion, with the peer's point in place of `G`: it \
      saves the callee-saved registers `x19`–`x25` in `scratch`; field elements are \
      six 64-bit words in Montgomery form, multiplied and squared by calls of `vg_p384_mul_mod_p` \
      and `vg_p384_sqr_mod_p` (the schedules of s2n-bignum's `bignum_montmul_p384_alt` and \
      `bignum_montsqr_p384_alt`: the full twelve-word product or square, six short Montgomery \
      reductions by the three nonzero words of `2^384 - p`, and a final conditional subtraction). \
      The peer's key is checked without branches (its first \
      byte, both coordinates below `p`, and the curve's equation), and the scalar multiplication \
      runs on the peer's point if it is valid, else `G`, so always on a point of the curve. `[d]P` \
      is by signed 4-bit windows: `d + 8 Σ_{j<97} 16^j` gives 97 digits in `[-8, 7]`; a table of \
      `[1 … 8]P` is built in `scratch` by the complete addition formulas of Renes, Costello and \
      Batina for `a = -3` (Algorithm 4), then brought into affine coordinates by one inversion \
      (Montgomery's trick: the prefix products of the entries' `Z`, one call of \
      `vg_p384_inv_mod_p`, and each entry's `Z⁻¹` from the last back). Then, from the point at \
      infinity, for each digit from the top, four doublings in Jacobian coordinates (dbl-2001-b, \
      with `Y = 1` where the result is the point at infinity) and the addition of the digit's \
      entry, every entry loaded and masked and `y` negated by a mask of the digit's sign. For \
      every digit but the last the addition is the mixed Jacobian one (madd-2004-hmv), whose \
      result is kept unless the accumulator or the entry is the point at infinity (selected by \
      masks of their `Z`): P-384 has prime order, so the operands are never equal or opposite \
      otherwise; the last digit's is by the complete formulas, in projective coordinates. Each \
      inversion (the table's, and `Z⁻¹` of the result) is a call of `vg_p384_inv_mod_p`, by divsteps (Bernstein and Yang's safegcd, half-delta form): 15 batches of 59 \
      divsteps on the low 64-bit words of `f` and `g` (from `f = p`, `g = Z`), each giving a matrix of \
      64-bit entries that updates `f`, `g` (divided by 2⁵⁹) and the coefficients `a`, `b` \
      (divided by 2⁶⁴ modulo `p`, as in Montgomery reduction), 885 divsteps in all, enough for \
      384-bit moduli by Bernstein and Yang's bound (which the proof checks); then `f = ±1`, and `Z⁻¹` is `a` times a \
      constant or its negation by `f`'s sign. The number of steps is fixed, so the time does not \
      depend on `Z`. The result (or zeros) is selected by a mask of the checks, `d` \
      in `[1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."]
    code := Impl.Ecdh.AArch64.exchangeP384
    verified := Proof.Ecdh.AArch64.P384.ecdh_verified h.law h.inv h.prime }]

end VG.Generic.P384.AArch64.EcdhP384
