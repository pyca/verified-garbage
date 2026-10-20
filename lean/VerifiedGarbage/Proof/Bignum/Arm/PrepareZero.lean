module

public import VerifiedGarbage.Impl.Bignum.Arm.MontInit
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Set the accumulator pointer and its extended word count -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_mov wp_dp op2_reg op2_imm dpVal)

theorem prepareZero_ok (s : State) {n : Nat} (count : s.gpr .r7 = BitVec.ofNat 32 n) :
    WP isa (.block prepareZero) s fun t => t.gpr .r0 = s.gpr .r6 ∧
      t.gpr .lr = BitVec.ofNat 32 (n + 2) ∧ t.gpr .r3 = 0 ∧ t.mem = s.mem ∧
      Rest [.r0, .r3, .lr] s t := by
  unfold prepareZero
  refine wp_mov (op2_reg _ _) fun s1 u1 => ?_
  refine wp_mov (op2_reg _ _) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u4 => WP.block_nil ?_
  refine ⟨?_, ?_, u4.gpr, ?_, ?_⟩
  · rw [u4.other .r0 (by decide), u3.other .r0 (by decide), u2.other .r0 (by decide), u1.gpr]
  · rw [u4.other .lr (by decide), u3.gpr, dpVal, u2.gpr, u1.other .r7 (by decide), count]
    change BitVec.ofNat 32 n + BitVec.ofNat 32 2 = _
    rw [← BitVec.ofNat_add]
  · rw [u4.mem, u3.mem, u2.mem, u1.mem]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans
      ((u3.rest (by simp)).trans (u4.rest (by simp))))

end VG.Proof.Bignum.Arm
