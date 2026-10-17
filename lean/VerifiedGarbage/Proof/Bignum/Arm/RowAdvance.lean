module

public import VerifiedGarbage.Impl.Bignum.Arm.Row
public import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The public pointer and counter update of an ARMv7 row -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_dp wp_subs op2_imm dpVal)

/-- The row's only branch condition is its public counter. -/
theorem rowAdvance_ok (s : State) :
    WP isa (.block rowAdvance) s fun t =>
      t.gpr .r0 = s.gpr .r0 + 4 ∧ t.gpr .r12 = s.gpr .r12 + 4 ∧
      t.gpr .lr = s.gpr .lr - 1 ∧ t.z = (s.gpr .lr - 1 == 0) ∧
      t.mem = s.mem ∧ Rest [.r0, .r12, .lr] s t := by
  unfold rowAdvance
  refine wp_dp (op2_imm (by decide)) fun s1 u1 => ?_
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  refine wp_subs (op2_imm (by decide)) fun s3 u3 hz => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u3.other .r0 (by decide), u2.other .r0 (by decide), u1.gpr, dpVal]
  · rw [u3.other .r12 (by decide), u2.gpr, dpVal, u1.other .r12 (by decide)]
  · rw [u3.gpr, u2.other .lr (by decide), u1.other .lr (by decide)]
  · rw [hz, u2.other .lr (by decide), u1.other .lr (by decide)]
  · rw [u3.mem, u2.mem, u1.mem]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans (u3.rest (by simp)))

end VG.Proof.Bignum.Arm
