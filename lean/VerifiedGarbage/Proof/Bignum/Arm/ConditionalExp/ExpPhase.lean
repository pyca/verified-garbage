module

public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpPhaseInput
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpStep
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.SquareOpCT

/-! # The ARMv7 RSA arithmetic phase implements the shared modular-exponentiation specification -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.ConditionalExp

open VG VG.Arm VG.Impl.Bignum.Arm
variable {ok : Prop} {Q : State → Prop} {regions : List Region}
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem expPhase_ok (s : State) {base ep : BitVec 32} {len w M x : Nat} {eb : List Byte}
    (K : TwoExp.Montgomery base len w Q regions) (h : ExpPhaseInput ok base ep len w M x eb s) (q : Q s)
    (sepR : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb.length⟩ r) :
    WP isa (expPhaseWith K.op) s fun t => ArithmeticReady base len w t ∧
      (ok → numAt t.mem (State.addr base) w 6 = Spec.Rsa.powMod x (Spec.Rsa.os2ip eb) M) ∧ Q t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [expPhaseWith, WP.seq_iff]
  refine WP.mono (expPhase_init_ready s K h q sepR) ?_
  rintro u ⟨⟨ready, qU⟩, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (expPhase_bytes_ready u K ready qU h.positive sepR) ?_
  rintro v ⟨power, qV, frameV, restV⟩
  refine WP.mono (exp_finish_ok v K power qV) ?_
  rintro t ⟨final, value, qT, _, frameT, restT⟩
  exact ⟨final, value, qT, frameU.trans (frameV.trans frameT), restU.trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm.ConditionalExp
