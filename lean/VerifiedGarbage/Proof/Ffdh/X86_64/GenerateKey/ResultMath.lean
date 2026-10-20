module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.PublicOutput
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Sample
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Math
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH on x86-64: generation's machine status matches the shared specification -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.Spec.Ffdh

/-- The scalar test rejects with 2; a power's range flag selects 1 or 3. -/
def resultStatus (p : GkP) (rb : List Byte) : Nat :=
  if p.sv = false then 2 else if p.fl rb then 1 else 3

theorem Base.power_value {p : GkP} {rb : List Byte} {s : X86_64.State} (h : Base p rb s)
    (hm : p.mv = true) : p.z rb = p.params.g ^ p.scalar rb % p.params.p := by
  change p.params.g ^ Spec.Rsa.os2ip (p.xb rb) % p.params.p = _
  rw [h.sample_value hm]

theorem Base.resultStatus_eq {p : GkP} {rb : List Byte} {s : X86_64.State} (h : Base p rb s)
    (hm : p.mv = true) (ha : parametersValid p.params = true) :
    resultStatus p rb = keyStatus p.params (p.scalar rb) := by
  cases hsv : p.sv with
  | false =>
    have hx : privateValid p.params (p.scalar rb) = false := h.valid.trans hsv
    have hr := (VG.Proof.Ffdh.keyStatus_scalar p.params (p.scalar rb)).mpr hx
    simpa only [resultStatus, hsv, ↓reduceIte] using hr.symm
  | true =>
    have hx : privateValid p.params (p.scalar rb) = true := h.valid.trans hsv
    rw [VG.Proof.Ffdh.keyStatus_power ha _ hx]
    simp only [resultStatus, hsv, Bool.true_eq_false, ↓reduceIte]
    congr 1
    apply propext
    change (1 < p.z rb ∧ 2 * (p.z rb / 2) + 1 < p.P) ↔ _
    rw [lt_pm1 (VG.Proof.Bignum.valid_facts hm h.k1).1, h.power_value hm]
    rfl

end VG.Proof.Ffdh.X86_64.GenerateKey
