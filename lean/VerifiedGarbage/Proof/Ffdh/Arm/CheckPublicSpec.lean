module

public import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicBody
import VerifiedGarbage.Proof.Ffdh.Domain

/-! Native public-value flags agree with the architecture-independent FFDH predicate. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG

theorem Inputs.domainP (p : Inputs) : (Spec.Ffdh.domainOf p.k p.dom).p = p.P := rfl

theorem Inputs.domainQ (p : Inputs) : (Spec.Ffdh.domainOf p.k p.dom).q =
    if p.hasQ = true then some p.Q else none := by
  change (if p.dom.length = 3 * p.k then some p.Q else none) = _
  rw [p.domainLength]
  by_cases hasQ : p.hasQ = true
  · rw [ite_eq_left hasQ, ite_eq_left rfl, ite_eq_left hasQ]
  · have different : 2 * p.k ≠ 3 * p.k := by have := p.minLength; omega
    rw [ite_eq_right hasQ, ite_eq_right different, ite_eq_right hasQ]

theorem publicFlag_spec (p : Inputs) (y : Nat) : publicFlag p y =
    if Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf p.k p.dom, y⟩ then 1 else 0 := by
  unfold Spec.Ffdh.publicValid
  rw [p.domainP, p.domainQ]
  by_cases hasQ : p.hasQ = true
  · rw [ite_eq_left hasQ]
    by_cases lo : 1 < y <;> by_cases hi : y < p.P - 1 <;>
      by_cases power : Spec.Rsa.powMod y p.Q p.P = 1 <;>
      simp [publicFlag, publicTailFlag, hasQ, lo, hi, power]
  · rw [ite_eq_right hasQ]
    by_cases lo : 1 < y <;> by_cases hi : y < p.P - 1 <;>
      simp [publicFlag, publicTailFlag, hasQ, lo, hi]

theorem checkedPublicFlag_spec (p : Inputs) (y : Nat) (valid : Spec.Ffdh.domainValid p.k p.dom = true) :
    checkedPublicFlag p y = if Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf p.k p.dom, y⟩ then 1 else 0 := by
  have modulus := VG.Proof.Ffdh.domainValid_mod valid
  rw [p.domainP] at modulus
  rw [checkedPublicFlag, ite_eq_left modulus, publicFlag_spec]

end VG.Proof.Ffdh.Arm
