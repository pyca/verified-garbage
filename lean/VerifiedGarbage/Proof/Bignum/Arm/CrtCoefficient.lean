module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtDifference
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Impl.Bignum.Arm.CrtCoefficient
public import VerifiedGarbage.Proof.Bignum.Arm.CrtInverseInput
import VerifiedGarbage.Proof.Bignum.Arm.CrtTimesInverse
import VerifiedGarbage.Proof.Bignum.Arm.CrtCoefficientMath
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Bignum.Arm.R2

/-! # The complete CRT recombination coefficient matches the signed RSA specification -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt
open VG.Spec.Rsa.Mont (numAt)
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
