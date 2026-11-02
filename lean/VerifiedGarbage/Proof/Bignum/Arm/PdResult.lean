module
public import VerifiedGarbage.Proof.Bignum.Arm.PdArithmetic
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpPhaseInput

import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpPhase
import VerifiedGarbage.Proof.Bignum.Arm.PublicAccepted
import VerifiedGarbage.Proof.Bignum.Arm.SquareRedCT

/-! # Precomputed exponentiation is safe unconditionally and computes RSA for valid R² -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure PdResult (base dst pp ep xp : BitVec 32) (len k eLen N R : Nat)
    (eb xb : List Byte) (s : State) : Prop where
  buffers : PublicData base dst ep xp len k eLen eb xb s
  stack : PublicStack base dst pp ep xp len k eLen s
  ready : ArithmeticReady base len (Spec.Rsa.modulusWords k) s
  positive : 0 < N
  value : pdGood k N R → numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) 6 =
    Spec.Rsa.powMod (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip eb) N
  flag : s.mem.readW (off (State.addr s.sp) 48) 32 = BitVec.ofNat 32 (decide (Spec.Rsa.os2ip xb < N)).toNat

theorem pdExponentiate_ok (s : State) {base dst pp ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb : List Byte}
    (h : PdAccepted base dst pp ep xp len k eLen N R eb xb s)
    (phase : ConditionalExp.ExpPhaseInput (pdGood k N R) base ep len (Spec.Rsa.modulusWords k) N (Spec.Rsa.os2ip xb) eb s) :
    WP isa expPhase s fun t => PdResult base dst pp ep xp len k eLen N R eb xb t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (ConditionalExp.expPhase_ok s phase) ?_
  rintro t ⟨ready, value, frame, rest⟩
  have positive : 0 < N := by have := h.ready.modulus; rw [h.modulus] at this; omega
  exact ⟨⟨h.buffers.after_workspace frame rest, h.stack.after_workspace frame rest, ready, positive, value,
    (h.stack.keep_acceptance frame rest).trans h.flag⟩, frame, rest⟩

end VG.Proof.Bignum.Arm
