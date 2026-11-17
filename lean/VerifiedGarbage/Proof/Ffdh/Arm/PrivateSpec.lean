module

public import VerifiedGarbage.Proof.Ffdh.Arm.PrivateBody
import VerifiedGarbage.Proof.Ffdh.Arm.DomainSpec
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicSpec

/-! Native private-key validation statuses agree with the shared FFDH algorithm. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG

/-- The flag's nest of tests and the status's, of the tests' outcomes: with a subgroup order and without. -/
private theorem flag_bool : ∀ a b c d e f : Bool,
    ((if a = true ∧ b = true then if c = true ∧ d = true then if e = true then if f = true then (1 : BitVec 32)
        else 0 else 0 else 0 else 2).toNat =
      if (a && b) = false then 2 else if (c && d && e) = true ∧ f = true then 1 else 0) ∧
    ((if a = true ∧ b = true then if c = true ∧ d = true then if f = true then (1 : BitVec 32) else 0 else 0
        else 2).toNat =
      if (a && b) = false then 2 else if (c && d && true) = true ∧ f = true then 1 else 0) := by
  decide

/-- `flag_bool`, of the tests: the statuses agree whatever the tests say, so that the proof below does not
take the seven tests of a key apart (128 cases, each simplified with every hypothesis). -/
private theorem flag_eq (A B C D E F : Prop) [Decidable A] [Decidable B] [Decidable C] [Decidable D]
    [Decidable E] [Decidable F] :
    ((if A ∧ B then if C ∧ D then if E then if F then (1 : BitVec 32) else 0 else 0 else 0 else 2).toNat =
      if (decide A && decide B) = false then 2 else
        if (decide C && decide D && decide E) = true ∧ F then 1 else 0) ∧
    ((if A ∧ B then if C ∧ D then if F then (1 : BitVec 32) else 0 else 0 else 2).toNat =
      if (decide A && decide B) = false then 2 else
        if (decide C && decide D && true) = true ∧ F then 1 else 0) := by
  simpa only [decide_eq_true_eq] using flag_bool (decide A) (decide B) (decide C) (decide D) (decide E) (decide F)

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
  by_cases hasQ : p.hasQ = true
  · simp only [hasQ, ↓reduceIte, Option.getD_some, VG.Proof.Bignum.powMod_eq, Bool.beq_eq_decide_eq]
    exact (flag_eq _ _ _ _ _ _).1
  · simp only [hasQ, VG.Proof.Bignum.powMod_eq]
    exact (flag_eq _ _ _ _ True _).2

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
