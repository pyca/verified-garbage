module

public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.Power
import VerifiedGarbage.Proof.Ffdh.Domain

/-! # FFDH private-key checks: scalar status and generated public values -/

@[expose] public section

namespace VG.Proof.Ffdh

open VG.Spec.Ffdh

/-- A rejected scalar has the distinguished status 2, independently of the
public value or whether the domain's other checks pass. -/
theorem privateStatus_scalar (a : Parameters) (y x : Nat) :
    privateStatus a y x = 2 ↔ privateValid a x = false := by
  unfold privateStatus
  cases hv : privateValid a x <;> simp only [Bool.not_false, Bool.not_true, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  split <;> decide

/-- Once the scalar is in range, a key pair is accepted exactly when the
computed power is nondegenerate and equals the imported public value. -/
theorem privateStatus_power {a : Parameters} (h : parametersValid a = true) (y x : Nat)
    (hx : privateValid a x = true) :
    privateStatus a y x = if (1 < a.g ^ x % a.p ∧ a.g ^ x % a.p < a.p - 1) ∧ a.g ^ x % a.p = y then 1 else 0 := by
  rw [privateStatus_eq h, hx]
  simp only [Bool.true_eq_false, ↓reduceIte]
  congr 1
  apply propext
  constructor
  · intro ⟨hy, he⟩
    exact ⟨(publicValid_power h x).mp (by rw [he]; exact hy), he⟩
  · intro ⟨hy, he⟩
    exact ⟨by rw [← he]; exact (publicValid_power h x).mpr hy, he⟩

end VG.Proof.Ffdh
