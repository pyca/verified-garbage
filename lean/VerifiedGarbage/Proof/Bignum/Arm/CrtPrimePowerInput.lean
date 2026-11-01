module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtPowerSources
public import VerifiedGarbage.Proof.Bignum.Arm.PrepareAcceptedPrime
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Layout

/-! # A validated factor becomes an arithmetic workspace while retaining its sources -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure CrtPrimePowerInput (base xp ep : BitVec 32) (len w k eLen slot : Nat)
    (xb eb : List Byte) (s : State) : Prop where
  accepted : AcceptedPrimeInput base len w s
  sources : CrtPowerSources base xp ep len w k eLen slot xb eb s

structure CrtPreparedPower (base xp ep : BitVec 32) (len w k eLen slot M : Nat)
    (xb eb : List Byte) (s : State) : Prop where
  ready : ArithmeticReady base len w s
  sources : CrtPowerSources base xp ep len w k eLen slot xb eb s
  modulus : numAt s.mem (State.addr base) w 0 = M
  odd : M % 2 = 1
  r2 : numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % M

theorem crt_primePower_prepare (s : State) {base xp ep : BitVec 32} {len w k eLen slot : Nat} {xb eb : List Byte}
    (h : CrtPrimePowerInput base xp ep len w k eLen slot xb eb s) (countFits : 128 * w < 2 ^ 32) :
    WP isa prepareAcceptedPrime s fun t =>
      let M := safePrime (s.mem.readW (off (State.addr s.sp) 48) 32).toNat (numAt s.mem (State.addr base) w 0)
      CrtPreparedPower base xp ep len w k eLen slot M xb eb t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have valid := safePrime_valid h.accepted.valid
  refine WP.mono (prepareAcceptedPrime_ok s h.accepted countFits) ?_
  rintro t ⟨done, modulus, r2, frame, rest⟩
  have ready : ArithmeticReady base len w t :=
    ⟨done.workspace, done.layout, done.width, done.ptr, done.inverse,
      by rw [modulus]; exact valid.1, done.stackRead, done.stackSep, done.saved⟩
  exact ⟨⟨ready, h.sources.after_workspace frame rest, modulus, valid.2, r2⟩, frame, rest⟩

end VG.Proof.Bignum.Arm
