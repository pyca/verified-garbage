module

public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.Power
import VerifiedGarbage.Proof.Ffdh.KeyScalar

/-! # FFDH key-generation status and generator powers -/

@[expose] public section

namespace VG.Proof.Ffdh

open VG.Spec.Ffdh

/-- The scalar rejection status is independent of all public-key checks. -/
theorem keyStatus_scalar (a : Parameters) (x : Nat) :
    keyStatus a x = 2 ↔ privateValid a x = false := by
  unfold keyStatus
  cases hv : privateValid a x <;>
    simp only [Bool.not_false, Bool.not_true, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  split <;> decide

/-- A checked generator's powers need only a range check to produce a key. -/
theorem keyStatus_power {a : Parameters} (h : parametersValid a = true) (x : Nat)
    (hx : privateValid a x = true) :
    keyStatus a x = if 1 < a.g ^ x % a.p ∧ a.g ^ x % a.p < a.p - 1 then 1 else 3 := by
  rw [KeyScalar.keyStatus_eq h, hx]
  simp only [Bool.true_eq_false, ↓reduceIte]
  congr 1
  exact propext (publicValid_power h x)

end VG.Proof.Ffdh
