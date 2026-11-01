module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtDifference
public import VerifiedGarbage.Impl.Bignum.Arm.CrtCoefficient
public import VerifiedGarbage.Proof.Bignum.Arm.CrtInverseInput

import VerifiedGarbage.Proof.Bignum.Arm.CrtCoefficientMath
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Bignum.Arm.R2
import VerifiedGarbage.Impl.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Arm.MontEncode
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperand
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
/-! # The complete CRT recombination coefficient matches the signed RSA specification -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/MontMixedProduct.lean`, which only this module imported.
section

/-! # Multiply an ordinary operand by a Montgomery-encoded operand -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem montMixedProduct_ok (s : State) {base : BitVec 32} {len w o a b M x y : Nat}
    (h : ArithmeticReady base len w s) (ho : Operand o) (ha : Operand a) (hb : Operand b) (ho0 : o ≠ 0)
    (modulus : numAt s.mem (State.addr base) w 0 = M) (odd : M % 2 = 1)
    (first : numAt s.mem (State.addr base) w a = x)
    (second : numAt s.mem (State.addr base) w b = y * 2 ^ (64 * w) % M) :
    WP isa (montOp o a b) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = M ∧ numAt t.mem (State.addr base) w o = x * y % M ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have positive : 0 < M := by have := h.modulus; rw [modulus] at this; omega
  refine WP.mono (montOp_ok s h ho ha hb ho0 (by rw [modulus, second]; exact Nat.mod_lt _ positive)) ?_
  rintro t ⟨ready, modT, bound, value, keeps, frame, rest⟩
  rw [modulus] at modT bound value
  rw [first, second, Nat.mul_mod_mod, ← Nat.mul_assoc] at value
  have result := mont_cancel (coprime_pow2 odd (64 * w)) value
  rw [Nat.mod_eq_of_lt bound] at result
  exact ⟨ready, modT, result, keeps, frame, rest⟩

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtTimesInverse.lean`, which only this module imported.
section

/-! # Exact multiplication by qInv in the factor workspace -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt
open VG.Proof.Rsa.Mont (numAt arrAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem crt_timesInverse_ok (s : State) {base src : BitVec 32} {len w k M : Nat} {bs : List Byte}
    (h : CrtInverseInput base src len w k M bs s) :
    WP isa timesInverse s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w 5 = numAt s.mem (State.addr base) w 5 * Spec.Rsa.os2ip bs % M ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  have op (q : Nat) (hq : q = 0 ∨ q = 1 ∨ q = 4 ∨ q = 5) : Operand q := by
    rcases hq with rfl | rfl | rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
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
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure CrtCoefficientInput (base src : BitVec 32) (len w k M : Nat) (bs : List Byte) (s : State) : Prop where
  difference : CrtDifferenceInput base len w M s
  source : SavedOperand base src len k 96 100 bs s
  positive : 0 < k
  fits : k ≤ 8 * w

theorem crt_coefficientDifference_ready (s : State) {base src : BitVec 32} {len w k M : Nat} {bs : List Byte}
    (h : CrtCoefficientInput base src len w k M bs s) :
    WP isa difference s fun t => CrtInverseInput base src len w k M bs t ∧
      numAt t.mem (State.addr base) w 5 =
        (numAt s.mem (State.addr base) w 6 + M - numAt s.mem (State.addr base) w 1 % M) % M ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (crt_difference_ok s h.difference) ?_
  rintro t ⟨ready, value, modulus, r2, _, frame, rest⟩
  exact ⟨⟨ready, modulus, h.difference.odd, r2, h.source.after_workspace frame rest, h.positive, h.fits⟩,
    value, frame, rest⟩

theorem crt_coefficient_ok (s : State) {base src : BitVec 32} {len w k M : Nat} {bs : List Byte}
    (h : CrtCoefficientInput base src len w k M bs s) :
    WP isa coefficient s fun t => ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w 5 =
        ((((numAt s.mem (State.addr base) w 6 : Int) - numAt s.mem (State.addr base) w 1) *
          Spec.Rsa.os2ip bs) % (M : Int)).toNat ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have positive : 0 < M := by have := h.difference.ready.modulus; rw [h.difference.modulus] at this; omega
  rw [coefficient, WP.seq_iff]
  refine WP.mono (crt_coefficientDifference_ready s h) ?_
  rintro u ⟨readyU, differenceU, frameU, restU⟩
  refine WP.mono (crt_timesInverse_ok u readyU) ?_
  rintro t ⟨ready, modulus, value, frameT, restT⟩
  rw [differenceU, crt_coefficient_value positive] at value
  exact ⟨ready, modulus, value, frameU.trans frameT, restU.trans restT⟩

end VG.Proof.Bignum.Arm
