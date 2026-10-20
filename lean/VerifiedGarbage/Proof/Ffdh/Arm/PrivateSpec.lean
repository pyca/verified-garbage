module

public import VerifiedGarbage.Proof.Ffdh.Arm.PrivateBody
import VerifiedGarbage.Proof.Ffdh.Arm.DomainSpec
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicSpec

/-! Native private-key validation statuses agree with the shared FFDH algorithm. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG

theorem checkedPrivateFlag_spec (p : Inputs) (yb xb : List Byte)
    (valid : Spec.Ffdh.domainValid p.k p.dom = true) :
    (checkedPrivateFlag p yb xb).toNat =
      Spec.Ffdh.privateStatus (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip yb) (Spec.Rsa.os2ip xb) := by
  have modulus := VG.Proof.Ffdh.domainValid_mod valid
  rw [p.domainP] at modulus
  have parameters : Spec.Ffdh.parametersValid (Spec.Ffdh.domainOf p.k p.dom) = true := by
    have h := valid
    rw [Spec.Ffdh.domainValid, Bool.and_eq_true] at h
    exact h.1
  rw [VG.Proof.Ffdh.privateStatus_eq parameters, checkedPrivateFlag, ite_eq_left modulus]
  unfold privateMainFlag privatePublicFlag privateTailFlag privateMatchFlag scalarBound
    Spec.Ffdh.privateValid Spec.Ffdh.publicValid
  rw [p.domainP, p.domainG, p.domainQ]
  by_cases hasQ : p.hasQ = true <;>
    by_cases scalarLo : 0 < Spec.Rsa.os2ip xb <;>
    by_cases scalarHi : Spec.Rsa.os2ip xb < (if p.hasQ = true then p.Q else p.P - 1) <;>
    by_cases publicLo : 1 < Spec.Rsa.os2ip yb <;>
    by_cases publicHi : Spec.Rsa.os2ip yb < p.P - 1 <;>
    by_cases member : Spec.Rsa.powMod (Spec.Rsa.os2ip yb) p.Q p.P = 1 <;>
    by_cases consistent : Spec.Rsa.powMod p.G (Spec.Rsa.os2ip xb) p.P = Spec.Rsa.os2ip yb <;>
    simp_all [VG.Proof.Bignum.powMod_eq]
  all_goals split_ifs <;> simp_all <;> omega

theorem privateStatus_two_iff (a : Spec.Ffdh.Parameters) (y x : Nat) :
    Spec.Ffdh.privateStatus a y x = 2 ↔ Spec.Ffdh.privateValid a x = false := by
  unfold Spec.Ffdh.privateStatus
  cases valid : Spec.Ffdh.privateValid a x
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false, Bool.true_eq_false]
    split <;> decide

theorem Inputs.privateValid_native (p : Inputs) (x : Nat) :
    Spec.Ffdh.privateValid (Spec.Ffdh.domainOf p.k p.dom) x = true ↔ 0 < x ∧ x < scalarBound p := by
  unfold Spec.Ffdh.privateValid scalarBound
  rw [p.domainP, p.domainQ]
  by_cases hasQ : p.hasQ = true <;> simp [hasQ]

theorem privateScalarClass_same (p : Inputs) (y x1 x2 : Nat)
    (status : Spec.Ffdh.privateStatus (Spec.Ffdh.domainOf p.k p.dom) y x1 =
      Spec.Ffdh.privateStatus (Spec.Ffdh.domainOf p.k p.dom) y x2) :
    (0 < x1 ∧ x1 < scalarBound p) ↔ (0 < x2 ∧ x2 < scalarBound p) := by
  have first := privateStatus_two_iff (Spec.Ffdh.domainOf p.k p.dom) y x1
  have second := privateStatus_two_iff (Spec.Ffdh.domainOf p.k p.dom) y x2
  simp only [Bool.eq_false_iff, ne_eq, p.privateValid_native] at first second
  constructor
  · intro good
    by_cases other : 0 < x2 ∧ x2 < scalarBound p
    · exact other
    · exact False.elim ((first.mp (status.trans (second.mpr other))) good)
  · intro good
    by_cases other : 0 < x1 ∧ x1 < scalarBound p
    · exact other
    · exact False.elim ((second.mp (status.symm.trans (first.mpr other))) good)

end VG.Proof.Ffdh.Arm
