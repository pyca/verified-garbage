module

public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpPhaseInput
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpStep
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.SquareRedCT

/-! # The ARMv7 RSA arithmetic phase implements the shared modular-exponentiation specification -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.ConditionalExp

variable {ok : Prop}
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem expPhase_ok (s : State) {base ep : BitVec 32} {len w M x : Nat} {eb : List Byte}
    (h : ExpPhaseInput ok base ep len w M x eb s) :
    WP isa expPhase s fun t => ArithmeticReady base len w t ∧
      (ok → numAt t.mem (State.addr base) w 6 = Spec.Rsa.powMod x (Spec.Rsa.os2ip eb) M) ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [expPhase, WP.seq_iff]
  refine WP.mono (expPhase_init_ready s h) ?_
  rintro u ⟨ready, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (expPhase_bytes_ready u ready h.positive) ?_
  rintro v ⟨power, frameV, restV⟩
  refine WP.mono (exp_finish_ok v power) ?_
  rintro t ⟨final, value, _, frameT, restT⟩
  exact ⟨final, value, frameU.trans (frameV.trans frameT), restU.trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm.ConditionalExp
