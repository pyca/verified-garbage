module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvInterface
import VerifiedGarbage.Proof.P384.Comb7
public import VerifiedGarbage.Impl.EcKey.P384.AArch64
import VerifiedGarbage.Proof.EcKey.AArch64.P384.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.EcKey.AArch64.P384.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.P384

/-!
# P-384 public keys (FIPS 186-5 §A.2) on AArch64

A generic file (see `TCB/Emit.lean`) over P-384's group law `h`, the variant
`Variants/P384/AArch64/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P384.AArch64.EcP384

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInvOrd Spec.P384.curve) : List Artifact := [
  Spec.EcKey.P384.publicKeyApi.artifact AArch64.target {
    notes := ["The function is `vg_ecdsa_p384_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it saves \
      the callee-saved registers `x19`–`x25` in `scratch`; field elements are six \
      64-bit words in Montgomery form, multiplied by calls of `vg_p384_mul_mod_p` (the schedule of \
      s2n-bignum's `bignum_montmul_p384_alt`: the full twelve-word product, six short Montgomery \
      reductions by the three nonzero words of `2^384 - p`, and a final conditional subtraction); \
      `[d]G` is `vg_ecdsa_p384_sign`'s fixed-base comb of 7-bit signed digits from the 55 tables \
      of `[m 2^(7j)]G` (`m = 1 … 64`) in the static `VG_P384_COMB`, each entry selected in \
      constant time by loading the whole table, with no doublings; and \
      `Z⁻¹` is a call of `vg_p384_inv_mod_p`, by divsteps (Bernstein and Yang's safegcd, half-delta form): 15 batches of 59 \
      divsteps on the low 64-bit words of `f` and `g` (from `f = p`, `g = Z`), each giving a matrix of \
      64-bit entries that updates `f`, `g` (divided by 2⁵⁹) and the coefficients `a`, `b` \
      (divided by 2⁶⁴ modulo `p`, as in Montgomery reduction), 885 divsteps in all, enough for \
      384-bit moduli by Bernstein and Yang's bound (which the proof checks); then `f = ±1`, and `Z⁻¹` is `a` times a \
      constant or its negation by `f`'s sign. The number of steps is fixed, so the time does not \
      depend on `Z`. The result (or zeros) is selected by a \
      mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."]
    consts := Impl.Ecdsa.AArch64.p384.combConsts
    code := Impl.EcKey.AArch64.publicKeyP384
    verified := Proof.EcKey.AArch64.P384.pk_verified h.law h.inv (Proof.P384.combOk7 h.law) }]

end VG.Generic.P384.AArch64.EcP384
