module

import VerifiedGarbage.Proof.Ffdh.Arm.DomainSpec
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleResult
import VerifiedGarbage.Proof.Ffdh.Arm.PrivateSpec
import VerifiedGarbage.Proof.Ffdh.Power
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicSpec

/-! The native attempt statuses and output encodings agree with the shared
FFDH specification, using subgroup closure for generated powers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem sampleMainFlag_spec (p : Inputs) (l : ScalarLayout p) (rb : List Byte) (_size : rb.length = p.k)
    (valid : Spec.Ffdh.domainValid p.k p.dom = true) :
    (sampleMainFlag p l rb).toNat = Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom)
      (Spec.Rsa.os2ip (l.encode rb)) := by
  have parameters : Spec.Ffdh.parametersValid (Spec.Ffdh.domainOf p.k p.dom) = true := by
    have h := valid
    rw [Spec.Ffdh.domainValid, Bool.and_eq_true] at h
    exact h.1
  have modulus := VG.Proof.Ffdh.domainValid_mod valid
  rw [p.domainP] at modulus
  have facts := VG.Proof.Bignum.valid_facts modulus p.minLength
  rw [VG.Proof.Ffdh.KeyScalar.keyStatus_eq parameters]
  have publicPower := VG.Proof.Ffdh.publicValid_power parameters (Spec.Rsa.os2ip (l.encode rb))
  have publicBool : Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf p.k p.dom,
      (Spec.Ffdh.domainOf p.k p.dom).g ^ Spec.Rsa.os2ip (l.encode rb) % (Spec.Ffdh.domainOf p.k p.dom).p⟩ =
      keyAccepted p (l.encode rb) := by
    have equiv : Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf p.k p.dom,
      (Spec.Ffdh.domainOf p.k p.dom).g ^ Spec.Rsa.os2ip (l.encode rb) % (Spec.Ffdh.domainOf p.k p.dom).p⟩ = true ↔
        keyAccepted p (l.encode rb) = true := by
      rw [publicPower, p.domainP, p.domainG]
      simp only [keyAccepted, keyPower, VG.Proof.Bignum.powMod_eq, decide_eq_true_eq]
    exact Bool.eq_iff_iff.mpr equiv
  rw [publicBool]
  have scalarClass := p.privateValid_native (Spec.Rsa.os2ip (l.encode rb))
  by_cases scalarGood : sampleScalarValid p l rb
  · have priv : Spec.Ffdh.privateValid (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip (l.encode rb)) = true :=
      scalarClass.mpr scalarGood
    rw [sampleMainFlag, ite_eq_left scalarGood, priv, ite_eq_right (by decide : ¬(true = false))]
    cases keyAccepted p (l.encode rb) <;> rfl
  · have priv : Spec.Ffdh.privateValid (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip (l.encode rb)) = false := by
      cases eq : Spec.Ffdh.privateValid (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip (l.encode rb))
      · rfl
      · exact False.elim (scalarGood (scalarClass.mp eq))
    rw [sampleMainFlag, ite_eq_right scalarGood, priv, ite_eq_left rfl]
    rfl

theorem sampleMainFlag_one (p : Inputs) (l : ScalarLayout p) (rb : List Byte) :
    (sampleMainFlag p l rb).toNat = 1 ↔ sampleSuccess p l rb = true := by
  unfold sampleMainFlag sampleSuccess
  by_cases valid : sampleScalarValid p l rb <;> cases accepted : keyAccepted p (l.encode rb) <;> simp [valid]

theorem sampleOctets_encoded (p : Inputs) (l : ScalarLayout p) (rb : List Byte) (size : rb.length = p.k)
    (valid : Spec.Ffdh.domainValid p.k p.dom = true) :
    l.encode rb = Spec.Rsa.i2osp (Spec.Rsa.os2ip (l.encode rb)) p.k := by
  have modulus := VG.Proof.Ffdh.domainValid_mod valid
  rw [p.domainP] at modulus
  have facts := VG.Proof.Bignum.valid_facts modulus p.minLength
  rw [← l.encode_length size]
  exact (VG.Proof.Rsa.i2osp_os2ip _).symm

theorem sampleResult_spec {p : Inputs} {l : ScalarLayout p} {rb : List Byte} {t : State} (size : rb.length = p.k)
    (valid : Spec.Ffdh.domainValid p.k p.dom = true) (result : sampleResult p l rb t) :
    (t.gpr .r0).toNat = Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom)
      (Spec.Rsa.os2ip (l.encode rb)) ∧
    if Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom)
        (Spec.Rsa.os2ip (l.encode rb)) = 1 then
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k =
        Spec.Rsa.i2osp (Spec.Rsa.os2ip (l.encode rb)) p.k ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.publicValue) p.k =
        Spec.Rsa.i2osp (Spec.Rsa.powMod (Spec.Ffdh.domainOf p.k p.dom).g
          (Spec.Rsa.os2ip (l.encode rb)) (Spec.Ffdh.domainOf p.k p.dom).p) p.k
    else Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k = List.replicate p.k 0 ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.publicValue) p.k = List.replicate p.k 0 := by
  obtain ⟨status, privateT, publicT⟩ := result
  have statusSpec := sampleMainFlag_spec p l rb size valid
  refine ⟨by rw [status]; exact statusSpec, ?_⟩
  by_cases success : Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom)
      (Spec.Rsa.os2ip (l.encode rb)) = 1
  · have native := (sampleMainFlag_one p l rb).mp (statusSpec.trans success)
    rw [native, ite_eq_left rfl] at privateT publicT
    rw [ite_eq_left success]
    refine ⟨privateT.trans (sampleOctets_encoded p l rb size valid), ?_⟩
    have modulus := VG.Proof.Ffdh.domainValid_mod valid
    rw [p.domainP] at modulus
    have facts := VG.Proof.Bignum.valid_facts modulus p.minLength
    rw [publicT, keyPower, p.domainP, p.domainG]
  · have native : sampleSuccess p l rb = false := by
      apply Bool.eq_false_iff.mpr
      intro good
      exact success (statusSpec.symm.trans ((sampleMainFlag_one p l rb).mpr good))
    rw [native, ite_eq_right (by decide : ¬(false = true))] at privateT publicT
    rw [ite_eq_right success]
    exact ⟨privateT, publicT⟩

end VG.Proof.Ffdh.Arm
