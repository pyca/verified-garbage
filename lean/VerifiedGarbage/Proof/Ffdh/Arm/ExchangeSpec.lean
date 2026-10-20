module

public import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeBody
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicSpec
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Ffdh.Arm.Context

/-! The native fixed-width shared value implements the shared exchange operation. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

theorem Inputs.exactWidth (p : Inputs) (valid : Spec.Ffdh.domainValid p.k p.dom = true) :
    (Spec.RsaKeyGen.bitLength p.P + 7) / 8 = p.k := by
  have top : 256 ^ (p.k - 1) ≤ p.P := by
    have h := valid
    simp only [Spec.Ffdh.domainValid, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2
  have bound := VG.Proof.Bignum.os2ip_lt (p.dom.take p.k)
  rw [p.pLength] at bound
  exact VG.Proof.Ffdh.octets_bitLength (by have := p.minLength; omega) top bound

theorem exchangeResult_spec {p : Inputs} {yb xb : List Byte} {t : State}
    (valid : Spec.Ffdh.domainValid p.k p.dom = true)
    (peer : Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf p.k p.dom, Spec.Rsa.os2ip yb⟩ = true)
    (result : exchangeResult p yb xb t) :
    Spec.Rsa.written t.mem (State.addr p.output) p.k (t.gpr .r0)
      (Spec.Ffdh.exchangeOp (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip yb)) := by
  have modulus := VG.Proof.Ffdh.domainValid_mod valid
  rw [p.domainP] at modulus
  have facts := VG.Proof.Bignum.valid_facts modulus p.minLength
  have operation := VG.Proof.Ffdh.exchangeOp_eq (k := p.k) (X := Spec.Rsa.os2ip xb) peer (by rw [p.domainP]; omega)
    (by rw [p.domainP]; exact p.exactWidth valid)
  rw [p.domainP] at operation
  rw [operation]
  have result := result
  unfold exchangeResult sharedAccepted sharedValue at result
  rw [VG.Proof.Bignum.powMod_eq] at result
  by_cases accepted : 1 < Spec.Rsa.os2ip yb ^ Spec.Rsa.os2ip xb % p.P ∧
      Spec.Rsa.os2ip yb ^ Spec.Rsa.os2ip xb % p.P < p.P - 1
  · rw [ite_eq_left accepted]
    simp [accepted] at result
    exact ⟨by rw [result.1] <;> rfl, result.2⟩
  · rw [ite_eq_right accepted]
    simp [accepted] at result
    exact ⟨by rw [result.1] <;> rfl, result.2⟩

end VG.Proof.Ffdh.Arm
