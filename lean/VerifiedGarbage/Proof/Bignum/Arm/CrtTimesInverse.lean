module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtInverseInput
public import VerifiedGarbage.Impl.Bignum.Arm.CrtCoefficient
import VerifiedGarbage.Proof.Bignum.Arm.MontMixedProduct
import VerifiedGarbage.Proof.Bignum.Arm.MontEncode
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperand
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block

/-! # Exact multiplication by qInv in the factor workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt
open VG.Spec.Rsa.Mont (numAt arrAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem crt_timesInverse_ok (s : State) {base src : BitVec 32} {len w k M : Nat} {bs : List Byte}
    (h : CrtInverseInput base src len w k M bs s) :
    WP isa timesInverse s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w 5 = numAt s.mem (State.addr base) w 5 * Spec.Rsa.os2ip bs % M ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  have op (q : Nat) (hq : q = 0 ∨ q = 1 ∨ q = 4 ∨ q = 5) : Operand q := by
    rcases hq with rfl | rfl | rfl | rfl <;> simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  rw [timesInverse, WP.seq_iff]
  refine WP.mono (savedOperand_ok s h.ready h.source (by decide : 1 < 8) (by decide) h.positive h.fits) ?_
  rintro u ⟨readyU, inverse, keepsU, frameU, restU⟩
  have modU := (keeps_array_num keepsU fits (op 0 (by simp)) (by decide)).trans h.modulus
  have r2U := (keeps_array_num keepsU fits (op 4 (by simp)) (by decide)).trans h.r2
  have differenceU := keeps_array_num keepsU fits (op 5 (by simp)) (by decide)
  rw [WP.seq_iff]
  refine WP.mono (montEncode_ok u readyU (op 1 (by simp)) (op 1 (by simp)) (by decide) modU h.odd r2U) ?_
  rintro v ⟨readyV, modV, encoded, keepsV, frameV, restV⟩
  rw [inverse] at encoded
  have differenceV := (keeps_array_num keepsV fits (op 5 (by simp)) (by decide)).trans differenceU
  refine WP.mono (montMixedProduct_ok v readyV (op 5 (by simp)) (op 5 (by simp)) (op 1 (by simp))
    (by decide) modV h.odd differenceV encoded) ?_
  rintro t ⟨ready, modulus, value, _, frameT, restT⟩
  exact ⟨ready, modulus, value, frameU.trans (frameV.trans frameT), restU.trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm
