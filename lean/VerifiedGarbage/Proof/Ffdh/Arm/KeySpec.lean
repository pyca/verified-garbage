module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBody
public import VerifiedGarbage.Proof.Ffdh.Arm.PrivateSpec
import VerifiedGarbage.Proof.Ffdh.Power
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math

/-! The native attempt statuses and output encodings agree with the shared
FFDH specification, using subgroup closure for generated powers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem keyMainFlag_spec (p : Inputs) (rb : List Byte) (size : rb.length = p.k)
    (valid : Spec.Ffdh.domainValid p.k p.dom = true) :
    (keyMainFlag p rb).toNat = Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom)
      (Spec.Ffdh.scalarOfOctets (Spec.Ffdh.domainOf p.k p.dom) rb) := by
  have parameters : Spec.Ffdh.parametersValid (Spec.Ffdh.domainOf p.k p.dom) = true := by
    have h := valid
    rw [Spec.Ffdh.domainValid, Bool.and_eq_true] at h
    exact h.1
  have modulus := VG.Proof.Ffdh.domainValid_mod valid
  rw [p.domainP] at modulus
  have facts := VG.Proof.Bignum.valid_facts modulus p.minLength
  have scalarValue := scalarOctets_value size facts.2.1 facts.1
  rw [← scalarValue, VG.Proof.Ffdh.KeyScalar.keyStatus_eq parameters]
  have publicPower := VG.Proof.Ffdh.publicValid_power parameters (Spec.Rsa.os2ip (scalarOctets p rb))
  have publicBool : Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf p.k p.dom,
      (Spec.Ffdh.domainOf p.k p.dom).g ^ Spec.Rsa.os2ip (scalarOctets p rb) % (Spec.Ffdh.domainOf p.k p.dom).p⟩ =
      keyAccepted p (scalarOctets p rb) := by
    have equiv : Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf p.k p.dom,
      (Spec.Ffdh.domainOf p.k p.dom).g ^ Spec.Rsa.os2ip (scalarOctets p rb) % (Spec.Ffdh.domainOf p.k p.dom).p⟩ = true ↔
        keyAccepted p (scalarOctets p rb) = true := by
      rw [publicPower, p.domainP, p.domainG]
      simp only [keyAccepted, keyPower, VG.Proof.Bignum.powMod_eq, decide_eq_true_eq]
    exact Bool.eq_iff_iff.mpr equiv
  rw [publicBool]
  have scalarClass := p.privateValid_native (Spec.Rsa.os2ip (scalarOctets p rb))
  by_cases scalarGood : keyScalarValid p rb
  · have priv : Spec.Ffdh.privateValid (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip (scalarOctets p rb)) = true :=
      scalarClass.mpr scalarGood
    rw [keyMainFlag, ite_eq_left scalarGood, priv, ite_eq_right (by decide : ¬(true = false))]
    cases keyAccepted p (scalarOctets p rb) <;> rfl
  · have priv : Spec.Ffdh.privateValid (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip (scalarOctets p rb)) = false := by
      cases eq : Spec.Ffdh.privateValid (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip (scalarOctets p rb))
      · rfl
      · exact False.elim (scalarGood (scalarClass.mp eq))
    rw [keyMainFlag, ite_eq_right scalarGood, priv, ite_eq_left rfl]
    rfl

theorem keyMainFlag_one (p : Inputs) (rb : List Byte) :
    (keyMainFlag p rb).toNat = 1 ↔ keySuccess p rb = true := by
  unfold keyMainFlag keySuccess
  by_cases valid : keyScalarValid p rb <;> cases accepted : keyAccepted p (scalarOctets p rb) <;> simp [valid]

theorem scalarOctets_encoded (p : Inputs) (rb : List Byte) (size : rb.length = p.k)
    (valid : Spec.Ffdh.domainValid p.k p.dom = true) :
    scalarOctets p rb = Spec.Rsa.i2osp (Spec.Ffdh.scalarOfOctets (Spec.Ffdh.domainOf p.k p.dom) rb) p.k := by
  have modulus := VG.Proof.Ffdh.domainValid_mod valid
  rw [p.domainP] at modulus
  have facts := VG.Proof.Bignum.valid_facts modulus p.minLength
  rw [← scalarOctets_value size facts.2.1 facts.1, ← scalarOctets_length size]
  exact (VG.Proof.Rsa.i2osp_os2ip _).symm

theorem keyResult_spec {p : Inputs} {rb : List Byte} {t : State} (size : rb.length = p.k)
    (valid : Spec.Ffdh.domainValid p.k p.dom = true) (result : keyResult p rb t) :
    (t.gpr .r0).toNat = Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom)
      (Spec.Ffdh.scalarOfOctets (Spec.Ffdh.domainOf p.k p.dom) rb) ∧
    if Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom)
        (Spec.Ffdh.scalarOfOctets (Spec.Ffdh.domainOf p.k p.dom) rb) = 1 then
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k =
        Spec.Rsa.i2osp (Spec.Ffdh.scalarOfOctets (Spec.Ffdh.domainOf p.k p.dom) rb) p.k ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.publicValue) p.k =
        Spec.Rsa.i2osp (Spec.Rsa.powMod (Spec.Ffdh.domainOf p.k p.dom).g
          (Spec.Ffdh.scalarOfOctets (Spec.Ffdh.domainOf p.k p.dom) rb) (Spec.Ffdh.domainOf p.k p.dom).p) p.k
    else Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k = List.replicate p.k 0 ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.publicValue) p.k = List.replicate p.k 0 := by
  obtain ⟨status, privateT, publicT⟩ := result
  have statusSpec := keyMainFlag_spec p rb size valid
  refine ⟨by rw [status]; exact statusSpec, ?_⟩
  by_cases success : Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom)
      (Spec.Ffdh.scalarOfOctets (Spec.Ffdh.domainOf p.k p.dom) rb) = 1
  · have native := (keyMainFlag_one p rb).mp (statusSpec.trans success)
    rw [native, ite_eq_left rfl] at privateT publicT
    rw [ite_eq_left success]
    refine ⟨privateT.trans (scalarOctets_encoded p rb size valid), ?_⟩
    have modulus := VG.Proof.Ffdh.domainValid_mod valid
    rw [p.domainP] at modulus
    have facts := VG.Proof.Bignum.valid_facts modulus p.minLength
    rw [publicT, keyPower, scalarOctets_value size facts.2.1 facts.1, p.domainP, p.domainG]
  · have native : keySuccess p rb = false := by
      apply Bool.eq_false_iff.mpr
      intro good
      exact success (statusSpec.symm.trans ((keyMainFlag_one p rb).mpr good))
    rw [native, ite_eq_right (by decide : ¬(false = true))] at privateT publicT
    rw [ite_eq_right success]
    exact ⟨privateT, publicT⟩

end VG.Proof.Ffdh.Arm
