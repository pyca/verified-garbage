module

public import VerifiedGarbage.Proof.Ed448.AArch64.BaseVerified
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Ed448 base-point multiplication on AArch64

The signature and documentation come from the reviewed Ed448 API.
-/

@[expose] public section

namespace VG.Artifacts.Ed448ScalarBase.AArch64

def artifacts : List Artifact := [
  Spec.Ed448.scalarBaseApi.artifact AArch64.target {
    notes := ["Computes `[s] B` with `vg_x448_base`'s comb \
      over all 57 bytes of the scalar: its 114 signed radix-16 digits select, in constant time \
      (reading every entry), entries `[m 256^j] B` (`m ≤ 8`) of 57 tables in the static \
      `VG_X448_COMB`, added to two projective \
      accumulators with RFC 8032's complete addition (a call of `vg_ed448_r56_comb_base`), then \
      `16 A + B` by five calls of `vg_ed448_r56_point_add`. `Z` is inverted with \
      X448's addition chain for `p - 2`. Field elements are eight 56-bit limbs, multiplied as \
      `vg_x448`'s are. The function saves its caller's callee-saved registers in `scratch`."]
    consts := Impl.X448.AArch64.Base.combConsts
    code := Impl.Ed448.AArch64.scalarBase
    verified := Proof.Ed448.AArch64.scalarBase_verified }]

end VG.Artifacts.Ed448ScalarBase.AArch64
