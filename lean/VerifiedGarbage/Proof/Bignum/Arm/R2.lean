module

public import VerifiedGarbage.Proof.Bignum.Arm.R2Init
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoop
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Complete R-squared computation from a valid RSA workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem r2_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) (countFits : 128 * w < 2 ^ 32) :
    WP isa r2 s fun t => DoubleLoopReady base len w 0 t ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [r2, WP.seq_iff]
  refine WP.mono (r2Init_ok s h) ?_
  rintro u ⟨ready, one, modulus, frame, rest⟩
  refine WP.mono (r2_from_one u ready countFits one) ?_
  rintro t ⟨next, value, modT, frameT, restT⟩
  rw [modulus] at value
  exact ⟨next, value, modT.trans modulus, frame.trans frameT, rest.trans restT⟩

end VG.Proof.Bignum.Arm
