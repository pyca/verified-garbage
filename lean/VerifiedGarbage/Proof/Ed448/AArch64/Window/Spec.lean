module

import VerifiedGarbage.Proof.Ed448.Group.Decode
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.Dbl
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.Table
public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Call
public import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem
public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Proof.X448.AArch64.Base.AddDefs

/-!
# Ed448 verification on AArch64: the equation, by the group law

Untrusted: everything here is checked by Lean. The group law's step from the
code's comparison of `[4]([S]B + [k](-A))` with `[4]R` to the specification's
equation (`four_iff`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Window

open VG.Proof.Ed448 (Rep dZ double double_rep identity_rep pointMul_rep pointAdd_rep pointEqual_rep
  decodePoint_rep baseAff basePoint_rep)
open VG.Proof.EdwardsLaw (EPoint)
open VG.Spec.Ed448 (Point)
open VG.Proof.X448 (addPt addPt_rep)

/-- `4 (x + y) = 4 z` exactly when `4 x = 4 z + 4 (-y)`. -/
theorem four_iff (x y z : EPoint dZ) :
    x + y + (x + y) + (x + y + (x + y)) = z + z + (z + z) ↔
      (4 : Nat) • x = (4 : Nat) • z + (4 : Nat) • (-y) := by
  have e1 : x + y + (x + y) + (x + y + (x + y)) = (4 : Nat) • x + (4 : Nat) • y := by abel
  have e2 : z + z + (z + z) = (4 : Nat) • z := by abel
  rw [e1, e2, smul_neg, ← sub_eq_add_neg, eq_sub_iff_add_eq]

end VG.Proof.Ed448.AArch64.Window
