module

import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont

import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
public import VerifiedGarbage.Impl.Bignum.AArch64.SquareEightCall
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall

@[expose] public section

namespace VG.Proof.Bignum.AArch64.SquareEightCall
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

theorem r2_keepsLink : (SquareEightDispatch.mm 4 4 4).allInstrs (fun i => vdstOf i != some .v31) = true := by
  decide +kernel

theorem y_keepsLink : (SquareEightDispatch.mm 6 6 6).allInstrs (fun i => vdstOf i != some .v31) = true := by
  decide +kernel

theorem no_v31 {o : Nat} (ho : o = 4 ∨ o = 6) :
    ∀ i ∈ instrs (SquareEightDispatch.mm o o o), vdstOf i ≠ some .v31 := by
  have h : (SquareEightDispatch.mm o o o).allInstrs (fun i => vdstOf i != some .v31) = true := by
    rcases ho with rfl | rfl
    · exact r2_keepsLink
    · exact y_keepsLink
  rw [Code.allInstrs_eq, List.all_eq_true] at h
  intro i hi he
  have hn := h i hi
  rw [he] at hn
  contradiction

end VG.Proof.Bignum.AArch64.SquareEightCall

namespace VG.Proof.Bignum.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum

/-- The scheduled Montgomery interface, with the two repeated squares shared
by calls. The fixed-slot helper contract is already reviewed and merged. -/
def Mont.calledSquareEight : Mont where
  mm := VG.Impl.Bignum.AArch64.SquareEightCall.mm
  ok := by
    intro s B Z w minv hg hz hw hw' o a b ho ha hb d1 d2 d3 d4 d5 d6 hi hv
    unfold VG.Impl.Bignum.AArch64.SquareEightCall.mm
    by_cases h : o = a ∧ a = b ∧ o = 6
    · rw [ite_eq_left h]
      obtain ⟨rfl, rfl, hs⟩ := h
      exact SquareCall.call_ok Mont.squareEight (SquareEightCall.no_v31 (Or.inr hs))
        hg hz hw hw' ho ha hb d1 d2 d3 d4 d5 d6 hi hv
    · rw [ite_eq_right h]
      exact Mont.calledSquare.ok hg hz hw hw' ho ha hb d1 d2 d3 d4 d5 d6 hi hv
  ct := by
    intro o a b huse
    unfold VG.Impl.Bignum.AArch64.SquareEightCall.mm
    by_cases h : o = a ∧ a = b ∧ o = 6
    · rw [ite_eq_left h]
      obtain ⟨rfl, rfl, _⟩ := h
      exact SquareCall.wrapper_ct (Mont.squareEight.ct huse)
    · rw [ite_eq_right h]
      exact Mont.calledSquare.ct huse

end VG.Proof.Bignum.AArch64
