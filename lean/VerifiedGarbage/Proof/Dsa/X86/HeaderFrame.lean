module
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Weierstrass

import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Mont.Words32

/-! # Disjoint fields in the saved argument header -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem field_separate {f other : Field} (h : f ≠ other) :
    Layout.field f + 4 ≤ Layout.field other ∨ Layout.field other + 4 ≤ Layout.field f := by
  cases f <;> cases other <;> simp_all [Layout.field]

theorem field_keep {s t : State} {base : Addr} {f other : Field}
    (O : Outside base (Layout.field f) 4 s.mem t.mem) (h : other ≠ f) :
    pointerValue base t (.input other) = pointerValue base s (.input other) := by
  have B := VG.Proof.Dsa.X86.Layout.field_bounds other
  have H := O.val32 (k := 1) (field_separate h) (by have : Layout.saved = 8256 := rfl; omega)
  apply BitVec.eq_of_toNat_eq
  simpa only [val32, w32, pointerValue, Nat.mul_zero, Nat.add_zero] using H

end VG.Proof.Dsa.X86
