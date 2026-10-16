module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimePowerReady
public import VerifiedGarbage.Proof.Bignum.Arm.SecretPower
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # One complete CRT modular power, with safe arithmetic on rejected inputs -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem crt_primePower_ok (s : State) {base xp ep : BitVec 32} {len w k eLen slot : Nat} {xb eb : List Byte}
    (h : CrtPrimePowerInput base xp ep len w k eLen slot xb eb s) (countFits : 128 * w < 2 ^ 32) :
    WP isa (primePower slot) s fun t =>
      let M := safePrime (s.mem.readW (off (State.addr s.sp) 48) 32).toNat (numAt s.mem (State.addr base) w 0)
      ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 6 = Spec.Rsa.powMod (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip eb) M ∧
      numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % M ∧
      numAt t.mem (State.addr base) w 7 = 1 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [primePower, WP.seq_iff]
  refine WP.mono (crt_primePower_prepare s h countFits) ?_
  rintro u ⟨prepared, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (crt_primePower_ready u prepared) ?_
  rintro v ⟨input, memV, restV⟩
  refine WP.mono (secretPower_ok v input) ?_
  rintro t ⟨ready, value, modulus, r2, one, frameT, restT⟩
  rw [memV] at frameT
  exact ⟨ready, value, modulus, r2, one, frameU.trans frameT,
    restU.trans ((restV.mono (by simp [roundClobbers])).trans restT)⟩

end VG.Proof.Bignum.Arm
