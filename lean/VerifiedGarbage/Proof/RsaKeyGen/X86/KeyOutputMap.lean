module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
import Mathlib.Tactic.IntervalCases

/-! # The seven output slots name distinct persistent arrays -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG.Impl.RsaKeyGen.X86.Key

theorem outputIndex_bound {i : Nat} (hi : i < 7) : outputIndex i < 32 := by
  interval_cases i <;> decide

theorem outputIndex_zero {i : Nat} (hi : i < 7) : VG.Impl.Rsa.X86.Keys.aZero ≠ outputIndex i := by
  interval_cases i <;> decide

theorem outputIndex_injective {i j : Nat} (hi : i < 7) (hj : j < 7) (ne : i ≠ j) :
    outputIndex i ≠ outputIndex j := by
  interval_cases i <;> interval_cases j <;> first | exact False.elim (ne rfl) | decide

end VG.Proof.RsaKeyGen.X86.Key
