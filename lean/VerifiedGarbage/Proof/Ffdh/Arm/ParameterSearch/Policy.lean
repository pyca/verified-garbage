module

public import VerifiedGarbage.Spec.Ffdh.Generation
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! Native-word bounds for the safe-prime controller's public search policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG

structure Policy (bits : Nat) : Prop where
  lower : 512 ≤ bits
  upper : bits ≤ 8192

theorem Policy.width_bounds {bits : Nat} (h : Policy bits) :
    64 ≤ (bits + 7) / 8 ∧ (bits + 7) / 8 ≤ 1024 := by
  have := h.lower
  have := h.upper
  omega

theorem Policy.attempts_bound {bits : Nat} (h : Policy bits) :
    Spec.Ffdh.parameterAttempts bits ≤ 2 ^ 32 := by
  have square := Nat.mul_le_mul h.upper h.upper
  unfold Spec.Ffdh.parameterAttempts
  omega

theorem Policy.entropy_bound {bits : Nat} (h : Policy bits) :
    Spec.Ffdh.parameterEntropy bits ≤ 33555456 := by
  have := h.width_bounds
  unfold Spec.Ffdh.parameterEntropy
  omega

theorem Policy.double_fits {bits available : Nat} (h : Policy bits)
    (bound : available ≤ Spec.Ffdh.parameterEntropy bits) :
    2 * max available (256 * ((bits + 7) / 8)) < 2 ^ 32 := by
  have width := h.width_bounds
  have entropy := h.entropy_bound
  have maximum : max available (256 * ((bits + 7) / 8)) ≤ 33555456 :=
    Nat.max_le.mpr ⟨by omega, by omega⟩
  omega

theorem Policy.request_bounds {bits available : Nat} (h : Policy bits) :
    512 * ((bits + 7) / 8) ≤ Spec.Ffdh.parameterRequest bits available ∧
      Spec.Ffdh.parameterRequest bits available ≤ Spec.Ffdh.parameterEntropy bits := by
  unfold Spec.Ffdh.parameterRequest Spec.Ffdh.parameterEntropy
  have width := h.width_bounds
  have maximum := Nat.le_max_right available (256 * ((bits + 7) / 8))
  constructor
  · exact Nat.le_min.mpr ⟨by omega, by omega⟩
  · exact Nat.min_le_right _ _

end VG.Proof.Ffdh.Arm.ParameterSearch
