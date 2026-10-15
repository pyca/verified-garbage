module

public import VerifiedGarbage.Proof.Bignum.Arm.PdInverse
public import VerifiedGarbage.Proof.Bignum.Arm.PdApply
public import VerifiedGarbage.Proof.Bignum.Arm.PdFail
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Public packed-key validation guards the precomputed arithmetic path -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

def PdOutput (dst : BitVec 32) (k N R : Nat) (eb xb : List Byte) (t : State) : Prop :=
  pdAccepted N R = true → pdGood k N R → N < 2 ^ (8 * k) →
    Spec.Rsa.bytesAt t.mem (State.addr dst) k =
      (if Spec.Rsa.os2ip xb < N then Spec.Rsa.i2osp (Spec.Rsa.powMod (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip eb) N) k
       else List.replicate k 0) ∧
    t.gpr .r0 = BitVec.ofNat 32 (decide (Spec.Rsa.os2ip xb < N)).toNat

theorem pdChecked_ok (s : State) {base dst pp ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb : List Byte}
    (h : PdBodyInput base dst pp ep xp len k eLen N R eb xb s)
    (check : PdCheckState base len (Spec.Rsa.modulusWords k) N R s) :
    WP isa PdFn.checked s fun t => PdOutput dst k N R eb xb t ∧
      Frame [⟨State.addr base, 8 * len⟩, ⟨off (State.addr s.sp) 48, 4⟩, ⟨State.addr dst, k⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [PdFn.checked, WP.seq_iff]
  refine WP.mono (pdChecks_ok s check) ?_
  rintro u ⟨checked, _, zero, frameU, restU⟩
  have hu := h.after_checks frameU restU checked.ready.ptr
  refine WP.ite (!(pdAccepted N R)) (by change some u.z = _; rw [zero]) ?_ ?_
  · intro invalid
    refine WP.mono (pdFail_ok u hu) ?_
    rintro t ⟨_, _, frameT, restT⟩
    refine ⟨?_, (frameU.mono (by simp)).trans (frameT.mono (by simp)), restU.trans restT⟩
    intro accepted
    simp only [accepted, Bool.not_true, Bool.false_eq_true] at invalid
  · intro valid
    have accepted : pdAccepted N R = true := by simpa using valid
    rw [PdFn.apply, WP.seq_iff]
    refine WP.mono (pdInverse_ok u hu checked accepted) ?_
    rintro v ⟨arithmetic, frameV, restV⟩
    refine WP.mono (pdApply_ok v arithmetic) ?_
    rintro t ⟨bytes, status, frameT, restT⟩
    rw [restV.sp, restU.sp] at frameT
    exact ⟨fun _ good bound => ⟨bytes good bound, status⟩,
      (frameU.mono (by simp)).trans ((frameV.mono (by simp)).trans frameT), restU.trans (restV.trans restT)⟩
end VG.Proof.Bignum.Arm
