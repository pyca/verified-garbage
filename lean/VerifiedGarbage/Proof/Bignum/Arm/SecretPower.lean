module

public import VerifiedGarbage.Proof.Bignum.Arm.SecretPowerImport
public import VerifiedGarbage.Proof.Bignum.Arm.SecretExpPhase
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A prepared private modular power implements the shared RSA specification -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem secretPower_ok (s : State) {base xp ep : BitVec 32} {len w k eLen M : Nat} {xb eb : List Byte}
    (h : SecretPowerInput base xp ep len w k eLen M xb eb s) :
    WP isa secretPower s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 6 = Spec.Rsa.powMod (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip eb) M ∧
      numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % M ∧
      numAt t.mem (State.addr base) w 7 = 1 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [secretPower, WP.seq_iff]
  refine WP.mono (secretPower_controls_ready s h) ?_
  rintro u ⟨hu, pointer, count, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (secretPower_import_ready u hu pointer count) ?_
  rintro v ⟨phase, frameV, restV⟩
  refine WP.mono (secretExpPhase_ok v phase) ?_
  rintro t ⟨ready, value, modulus, r2, one, frameT, restT⟩
  exact ⟨ready, value, modulus, r2, one, frameU.trans (frameV.trans frameT),
    (restU.mono (by simp)).trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm
