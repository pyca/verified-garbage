module

import VerifiedGarbage.Impl.Bignum.Arm.CombDigit
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.TCB.Arm.Isa

/-! The bounded public index comparison needs only the existing Z condition. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombDigit
open VG VG.Arm VG.Proof.X25519.Arm

theorem guard_value {k N : Nat} (hk : k < 2^31) (hn : N < 2^31) :
    (BitVec.ofNat 32 k - BitVec.ofNat 32 N) >>> 31 = if k<N then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : k < 2^32), Nat.mod_eq_of_lt (by omega : N < 2^32)]
  simp only [Nat.shiftRight_eq_div_pow]
  split
  · rw [show (1 : BitVec 32).toNat = 1 by decide]
    omega
  · rw [show (0 : BitVec 32).toNat = 0 by decide]
    omega

theorem guard_ok (s : State) {k N : Nat} (hk : k < 2^31) (hn : N < 2^31)
    (index : s.gpr .r9 = BitVec.ofNat 32 k) (width : s.gpr .r8 = BitVec.ofNat 32 N) :
    WP isa (.block [.dp .sub .r12 .r9 (.reg .r8), .mov .r12 (.shifted .r12 .lsr 31),
      .cmp .r12 (.imm 0)]) s fun t =>
      t.z = !decide (k<N) ∧ t.mem = s.mem ∧ Rest [.r12] s t := by
  refine wp_dp (op2_reg _ _) fun u one => ?_
  refine wp_mov (by rfl) fun v two => ?_
  refine wp_cmp (op2_imm (by decide)) fun t three zero => WP.block_nil ?_
  have value : v.gpr .r12 = if k<N then 1 else 0 := by
    rw [two.gpr,one.gpr]
    change (s.gpr .r9 - s.gpr .r8) >>> 31 = _
    rw [index,width,guard_value hk hn]
  refine ⟨?_,three.mem.trans (two.mem.trans one.mem),
    ((one.rest (by simp)).trans (two.rest (by simp))).trans (three.rest _)⟩
  rw [zero,value]
  by_cases h : k<N
  · simp only [ite_eq_left h,decide_eq_true h]
    rfl
  · simp only [ite_eq_right h,decide_eq_false h]
    rfl

end VG.Proof.Bignum.Arm.CombDigit
