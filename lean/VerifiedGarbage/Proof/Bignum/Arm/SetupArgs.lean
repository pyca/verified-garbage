module

public import VerifiedGarbage.Impl.Bignum.Arm.Setup
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Initial pointers and stride for the RSA array-header loop -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_mov wp_dp op2_reg op2_lsl op2_imm dpVal)

theorem setupArgs_ok (s : State) {w : Nat} (count : s.gpr .r7 = BitVec.ofNat 32 w) :
    WP isa (.block setupArgs) s fun t =>
      t.gpr .r8 = s.gpr .r0 ∧ t.gpr .r0 = s.gpr .r0 + BitVec.ofNat 32 64 ∧
      t.gpr .r4 = s.gpr .r0 + BitVec.ofNat 32 256 ∧
      t.gpr .r5 = BitVec.ofNat 32 (8 * (w + 2)) ∧ t.gpr .lr = BitVec.ofNat 32 8 ∧
      t.mem = s.mem ∧ Rest [.r0, .r4, .r5, .r8, .lr] s t := by
  unfold setupArgs
  refine wp_mov (op2_reg _ _) fun s1 u1 => ?_
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  refine wp_mov (op2_lsl (by decide)) fun s3 u3 => ?_
  refine wp_dp (op2_imm (by decide)) fun s4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun s5 u5 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u6 => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, u6.gpr, ?_, ?_⟩
  · rw [u6.other .r8 (by decide), u5.other .r8 (by decide), u4.other .r8 (by decide),
      u3.other .r8 (by decide), u2.other .r8 (by decide), u1.gpr]
  · rw [u6.other .r0 (by decide), u5.gpr, dpVal, u4.other .r0 (by decide),
      u3.other .r0 (by decide), u2.other .r0 (by decide), u1.other .r0 (by decide)]
    rfl
  · rw [u6.other .r4 (by decide), u5.other .r4 (by decide), u4.gpr, dpVal,
      u3.other .r0 (by decide), u2.other .r0 (by decide), u1.other .r0 (by decide)]
    rfl
  · rw [u6.other .r5 (by decide), u5.other .r5 (by decide), u4.other .r5 (by decide),
      u3.gpr, u2.gpr, dpVal, u1.other .r7 (by decide), count]
    change (BitVec.ofNat 32 w + BitVec.ofNat 32 2) <<< 3 = _
    rw [← BitVec.ofNat_add, BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 32 (w + 2) * BitVec.ofNat 32 8 = _
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  · rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans
      ((u3.rest (by decide)).trans ((u4.rest (by decide)).trans
        ((u5.rest (by decide)).trans (u6.rest (by decide))))))

end VG.Proof.Bignum.Arm
