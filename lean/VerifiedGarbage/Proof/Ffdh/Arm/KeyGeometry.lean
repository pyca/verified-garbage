module

public import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Proof.Ffdh.Lead
import VerifiedGarbage.Proof.Ffdh.KeyScalar

/-! The public bound determines the fixed scalar mask and exponent width. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem Inputs.domainLengths (p : Inputs) : p.dom.length = 2 * p.k ∨ p.dom.length = 3 * p.k := by
  rw [p.domainLength]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem Inputs.boundOctetsLength (p : Inputs) : p.boundOctets.length = p.k :=
  VG.Proof.Ffdh.KeyScalar.bnd_length p.domainLengths

theorem Inputs.boundOctetsQ (p : Inputs) (hasQ : p.hasQ = true) :
    p.boundOctets = (p.dom.drop (2 * p.k)).take p.k := by
  unfold Inputs.boundOctets VG.Proof.Ffdh.KeyScalar.bnd
  have length : p.dom.length = 3 * p.k := by rw [p.domainLength, ite_eq_left hasQ]
  rw [ite_eq_left length]

theorem Inputs.boundOctetsP (p : Inputs) (hasQ : p.hasQ = false) : p.boundOctets = p.dom.take p.k := by
  unfold Inputs.boundOctets VG.Proof.Ffdh.KeyScalar.bnd
  have length : p.dom.length ≠ 3 * p.k := by
    rw [p.domainLength, hasQ]
    simp only [Bool.false_eq_true, ite_false]
    have := p.minLength; omega
  rw [ite_eq_right length]

theorem Inputs.scalarLeadBound (p : Inputs) : p.scalarLead < p.k := by
  have nonempty : p.boundOctets ≠ [] := by
    intro empty
    have size := p.boundOctetsLength
    rw [empty] at size
    have := p.minLength
    simp only [List.length_nil] at size
    omega
  have bound := VG.Proof.Ffdh.lead_lt nonempty
  rw [p.boundOctetsLength] at bound
  exact bound

theorem Inputs.scalarWidthBounds (p : Inputs) : 0 < p.scalarWidth ∧ p.scalarWidth ≤ p.k := by
  have := p.scalarLeadBound
  unfold Inputs.scalarWidth
  omega

theorem Context.boundBytes {p : Inputs} {slots : List Nat} {s : State} (h : Context p slots s) :
    Octets p.base p.boundSource p.len p.boundOctets s := by
  cases hasQ : p.hasQ
  · rw [Inputs.boundSource, ite_eq_right (by rw [hasQ]; decide), p.boundOctetsP hasQ]
    exact h.pBytes
  · rw [Inputs.boundSource, ite_eq_left hasQ, p.boundOctetsQ hasQ]
    exact h.qBytes hasQ

end VG.Proof.Ffdh.Arm
