module

public import VerifiedGarbage.Proof.Bignum.Arm.ExpPhaseInput
public import VerifiedGarbage.Proof.Bignum.Arm.SecretExpBytes
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Private RSA exponentiation implements the shared modular-exponentiation specification -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem secretExpPhase_ok (s : State) {base ep : BitVec 32} {len w M x : Nat} {eb : List Byte}
    (h : ExpPhaseInput base ep len w M x eb s) :
    WP isa secretExpPhase s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 6 = Spec.Rsa.powMod x (Spec.Rsa.os2ip eb) M ∧
      numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % M ∧
      numAt t.mem (State.addr base) w 7 = 1 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [secretExpPhase, WP.seq_iff]
  refine WP.mono (expPhase_init_ready s h) ?_
  rintro u ⟨ready, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (secretExpBytes_ok u ready.power h.positive ready.countFit ready.sourceFit ready.read ready.separate ready.bytes
    (by simpa only [BitVec.add_zero] using ready.pointer) ready.count) ?_
  rintro v ⟨power, frameV, restV⟩
  refine WP.mono (exp_finish_ok v power) ?_
  rintro t ⟨final, value, keeps, frameT, restT⟩
  have fits : Spec.Rsa.Mont.arrAt w 8 ≤ 8 * len := power.ready.width ▸ power.ready.layout.2.2.1
  have modulus := (keeps_array_num keeps fits (q := 0)
    (by simp [Spec.Rsa.Mont.Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) (by decide)).trans power.modulus
  have r2 := (keeps_array_num keeps fits (q := 4)
    (by simp [Spec.Rsa.Mont.Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) (by decide)).trans power.r2
  have one := (keeps_array_num keeps fits (q := 7)
    (by simp [Spec.Rsa.Mont.Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) (by decide)).trans power.one
  exact ⟨final, value, modulus, r2, one, frameU.trans (frameV.trans frameT), restU.trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm
