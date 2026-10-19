module
public import VerifiedGarbage.Impl.Bignum.AArch64.SquareCall
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcMont

@[expose] public section

namespace VG.Proof.Bignum.AArch64.SquareCall
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

theorem r2_noVec : (BlockedRedc.mm 4 4 4).allInstrs (fun i => (vdstOf i).isNone) = true := by
  decide +kernel

theorem y_noVec : (BlockedRedc.mm 6 6 6).allInstrs (fun i => (vdstOf i).isNone) = true := by
  decide +kernel

theorem no_v31 {o : Nat} (ho : o = 4 ∨ o = 6) :
    ∀ i ∈ instrs (BlockedRedc.mm o o o), vdstOf i ≠ some .v31 := by
  have h : (BlockedRedc.mm o o o).allInstrs (fun i => (vdstOf i).isNone) = true := by
    rcases ho with rfl | rfl
    · exact r2_noVec
    · exact y_noVec
  rw [Code.allInstrs_eq, List.all_eq_true] at h
  intro i hi he
  have hn := h i hi
  rw [he] at hn
  contradiction

end VG.Proof.Bignum.AArch64.SquareCall

namespace VG.Proof.Bignum.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum

/-- The same Montgomery interface, with the two repeated squares shared
by calls. The helper contracts are registered separately from their callers. -/
def Mont.calledSquare : Mont where
  mm := VG.Impl.Bignum.AArch64.SquareCall.mm
  ok := by
    intro s B Z w minv hg hz hw hw' o a b ho ha hb d1 d2 d3 d4 d5 d6 hi hv
    unfold VG.Impl.Bignum.AArch64.SquareCall.mm
    by_cases h : o = a ∧ a = b ∧ (o = 4 ∨ o = 6)
    · rw [ite_eq_left h]
      obtain ⟨rfl, rfl, hs⟩ := h
      exact SquareCall.call_ok Mont.blocked (SquareCall.no_v31 hs)
        hg hz hw hw' ho ha hb d1 d2 d3 d4 d5 d6 hi hv
    · rw [ite_eq_right h]
      exact Mont.blocked.ok hg hz hw hw' ho ha hb d1 d2 d3 d4 d5 d6 hi hv
  ct := by
    intro o a b huse
    unfold VG.Impl.Bignum.AArch64.SquareCall.mm
    by_cases h : o = a ∧ a = b ∧ (o = 4 ∨ o = 6)
    · rw [ite_eq_left h]
      obtain ⟨rfl, rfl, _⟩ := h
      exact SquareCall.wrapper_ct (Mont.blocked.ct huse)
    · rw [ite_eq_right h]
      exact Mont.blocked.ct huse

end VG.Proof.Bignum.AArch64
