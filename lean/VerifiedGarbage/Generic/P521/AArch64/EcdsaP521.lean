module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
import VerifiedGarbage.Proof.P521.Comb7
import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
public import VerifiedGarbage.Impl.Ecdsa.Verify.P521.AArch64
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.AArch64Instrs
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Spec.Ecdsa.Verify.P521
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointVerified

/-!
# ECDSA over P-521 (FIPS 186-5) on AArch64

A generic file (see `TCB/Emit.lean`) over P-521's group law `h`, the variant
`Variants/P521/AArch64/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P521.AArch64.EcdsaP521

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvOrd Spec.P521.curve) : List Artifact := [
  Spec.Ecdsa.P521.signApi.artifact AArch64.target {
    notes := ["The function saves the callee-saved registers \
      `x19`–`x25` in `scratch`. Field elements and scalars are nine 64-bit words in \
      Montgomery form, field elements multiplied by calls of `vg_p521_mul_mod_p` (word-by-word \
      Montgomery multiplication with all of `[b]` in registers, whose reductions are shifts, \
      P-521's `p` being friendly, and a final conditional subtraction), and scalars multiplied by \
      calls of `vg_p521_mul_mod_n` (word-by-word Montgomery multiplication, CIOS, with a final \
      conditional subtraction). `[k]G` is a fixed-base comb of 7-bit signed digits: the 83 windows \
      `k_j` of \
      `k`'s bits as digits `k_j - 64` from `-64` to `63`, `[k]G = [64 Σ 2^(7j)]G + Σ [(k_j - 64) \
      2^(7j)]G`, from 83 tables of `[m 2^(7j)]G` (`m = 1 … 64`, affine, in Montgomery form) in the \
      static `VG_P521_COMB` (747 KB), with no doublings: each entry is selected in constant time by \
      loading every entry of its table and keeping, with `csel`, the one of the digit's magnitude \
      (or the point at infinity for a zero digit), its `x` in one pass over the table and its `y` \
      in another, negated by a mask of its sign, and added by the complete addition formulas of \
      Renes, Costello and Batina for `a = -3` (Algorithm 4: 12 products and 2 by `b`); the \
      inversions modulo `p` and `n` are \
      by divsteps (Bernstein and Yang's safegcd, half-delta form): 23 batches of 59 \
      divsteps on the low 64-bit words of `f` and `g` (from `f = p`, `g = Z`, or `n` and `k`), each giving a matrix of \
      64-bit entries that updates `f`, `g` (divided by 2⁵⁹) and the coefficients `a`, `b` \
      (divided by 2⁶⁴ modulo `p` or `n`, as in Montgomery reduction), 1357 divsteps in all, enough for \
      576-bit moduli by Bernstein and Yang's bound (which the proof checks); then `f = ±1`, and `Z⁻¹` is `a` times a \
      constant or its negation by `f`'s sign. The number of steps is fixed, so the time does not \
      depend on `Z` or `k`. The signature \
      (or zeros) is selected by a mask, so the time depends only on the pointers."]
    consts := Impl.Ecdsa.AArch64.p521.combConsts
    code := Impl.Ecdsa.AArch64.signP521
    verified := Proof.Ecdsa.AArch64.P521.sign_verified h.law h.inv (Proof.P521.combOk7 h.law) },
  Spec.Ecdsa.P521.verifyApi.artifact AArch64.target {
    notes := ["The function validates the public key and signature and computes \
      `[u]G + [v]Q` with one interleaved Jacobian doubling chain. Public width-seven NAF \
      digits select affine generator multiples from the first row of `VG_P521_COMB`; \
      public width-five NAF digits select eight odd peer multiples built with co-Z \
      arithmetic, with cached `Z²` and `Z³` packed into the existing scratch space. \
      Both recodings cover 577 positions. Nonzero generator digits use mixed Jacobian \
      addition; peer digits use the cached Jacobian addition, including exceptional cases. \
      Nine-word field products use Montgomery multiplication, and field squares use the \
      dedicated symmetric P-521 square with Mersenne reduction. The scalar inverse uses \
      fixed-count divsteps. Invalid keys are replaced with the generator for arithmetic, \
      while the final mask retains all original validity checks. Projective comparisons \
      test `X = rZ` and, when applicable, `X = (r+n)Z` without a final inversion. \
      The function preserves the original verification contract and scratch size; \
      branches and table addresses depend only on the public key, digest and signature."]
    consts := Impl.Ecdsa.AArch64.p521.combConsts
    code := Impl.Ecdsa.Verify.AArch64.verifyP521
    verified := Proof.Ecdsa.Verify.AArch64.P521.verify_verified h.law h.prime h.inv (Proof.P521.combOk7 h.law) }]

end VG.Generic.P521.AArch64.EcdsaP521
