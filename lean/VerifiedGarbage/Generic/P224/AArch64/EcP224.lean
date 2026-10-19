module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.P224.Comb7
public import VerifiedGarbage.Impl.EcKey.P224.AArch64
import VerifiedGarbage.Proof.EcKey.AArch64.P224.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Tactic.ClearExcept
public import VerifiedGarbage.Proof.EcKey.AArch64.P224.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.P224

/-!
# P-224 public keys (FIPS 186-5 §A.2) on AArch64

A generic file (see `TCB/Emit.lean`) over P-224's group law `h`, the variant
`Variants/P224/AArch64/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P224.AArch64.EcP224

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.P224.curve) : List Artifact := [
  Spec.EcKey.P224.publicKeyApi.artifact AArch64.target {
    notes := ["The function is `vg_ecdsa_p224_sign`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it saves \
      the callee-saved registers `x19`–`x25` in `scratch`; field elements are four 64-bit words \
      in Montgomery form, multiplied by word-by-word Montgomery multiplication (CIOS, with `mul` \
      and `umulh` and the multiplicand's words in registers; each reduction step multiplies the \
      accumulator's low word by `-p⁻¹ mod 2⁶⁴` and adds that multiple of `p`) with a final \
      conditional subtraction; `[d]G` is `vg_ecdsa_p224_sign`'s fixed-base comb of 7-bit signed \
      digits from the 37 tables of `[m 2^(7j)]G` (`m = 1 … 64`) in the static `VG_P224_COMB`, \
      each entry selected in constant time by loading the whole table, with no doublings; and \
      `Z⁻¹` is a call of `vg_p224_inv_mod_p`, by divsteps (Bernstein and Yang's safegcd, half-delta form): 10 batches of 59 \
      divsteps on the low 64-bit words of `f` and `g` (from `f = p`, `g = Z`), each giving a \
      matrix of 64-bit entries that updates `f`, `g` (divided by 2⁵⁹) and the coefficients `a`, \
      `b` (divided by 2⁶⁴ modulo `p`, as in Montgomery reduction), 590 divsteps in all, enough \
      for 256-bit moduli by Bernstein and Yang's bound (which the proof checks); then `f = ±1`, \
      and `Z⁻¹` is `a` times a constant or its negation by `f`'s sign. The number of steps is \
      fixed, so the time does not depend on `Z`. The result (or zeros) is selected by a mask of \
      `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."]
    consts := Impl.Ecdsa.AArch64.p224.combConsts
    code := Impl.EcKey.AArch64.publicKeyP224
    verified := Proof.EcKey.AArch64.P224.pk_verified h.law h.inv (Proof.P224.combOk7 h.law) }]

end VG.Generic.P224.AArch64.EcP224
