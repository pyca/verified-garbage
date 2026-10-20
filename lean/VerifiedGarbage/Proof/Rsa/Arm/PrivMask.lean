module

public import VerifiedGarbage.Impl.Rsa.Arm.PrivChecked
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.AesGcm.Arm.Compare
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate

/-! # Branchless fault status and the mask controlling private-result release -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked
open VG.Proof.X25519.Arm (Rest wp_mov wp_dp op2_imm op2_reg op2_lsr dpVal)

theorem zero_test32 (x : BitVec 32) : 1#32 - (((0#32 - x) ||| x) >>> 31) = BitVec.ofNat 32 (decide (x = 0#32)).toNat := by
  have shift := VG.Proof.AesGcm.Arm.msb_or_neg x
  change (x ||| (0#32 - x)) >>> 31 = (if x = 0#32 then 0#32 else 1#32) at shift
  rw [BitVec.or_comm, shift]
  by_cases h : x = 0#32 <;> simp [h]

theorem maskCore_ok (s : State) {accepted equal : Bool}
    (good : s.gpr .r4 = BitVec.ofNat 32 accepted.toNat) (eq : (s.gpr .r2 = 0) ↔ equal = true) :
    WP isa (.block maskCore) s fun t =>
      t.gpr .r2 = -BitVec.ofNat 32 (accepted && equal).toNat ∧
      t.gpr .r4 = (if accepted then if equal then 1 else 2 else 0) ∧
      t.mem = s.mem ∧ Rest [.r2, .r3, .r4, .r12] s t := by
  unfold maskCore
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => ?_
  refine wp_mov (op2_imm (by decide)) fun s5 u5 => ?_
  refine wp_dp (op2_reg _ _) fun s6 u6 => ?_
  have eq6 : s6.gpr .r3 = BitVec.ofNat 32 equal.toNat := by
    rw [u6.gpr, dpVal, u5.gpr, u5.other .r3 (by decide), u4.gpr,
      u3.gpr, dpVal, u2.gpr, dpVal, u1.gpr, u1.other .r2 (by decide),
      u2.other .r2 (by decide), u1.other .r2 (by decide)]
    change 1#32 - (((0#32 - s.gpr .r2) ||| s.gpr .r2) >>> 31) = _
    rw [zero_test32]
    have eq' : (s.gpr .r2 = 0#32) ↔ equal = true := eq
    simp only [eq', Bool.decide_eq_true]
  refine wp_dp (op2_reg _ _) fun s7 u7 => ?_
  refine wp_mov (op2_imm (by decide)) fun s8 u8 => ?_
  refine wp_dp (op2_reg _ _) fun s9 u9 => ?_
  refine wp_dp (op2_reg _ _) fun s10 u10 => ?_
  refine wp_mov (op2_imm (by decide)) fun s11 u11 => ?_
  refine wp_dp (op2_reg _ _) fun s12 u12 => ?_
  refine wp_dp (op2_reg _ _) fun t u13 => WP.block_nil ?_
  have good6 : s6.gpr .r4 = BitVec.ofNat 32 accepted.toNat := by
    rw [u6.other .r4 (by decide), u5.other .r4 (by decide), u4.other .r4 (by decide),
      u3.other .r4 (by decide), u2.other .r4 (by decide), u1.other .r4 (by decide), good]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [u13.other .r2 (by decide), u12.other .r2 (by decide), u11.other .r2 (by decide),
      u10.other .r2 (by decide), u9.gpr, dpVal, u8.gpr, u8.other .r2 (by decide), u7.gpr, dpVal, good6, eq6]
    cases accepted <;> cases equal <;> rfl
  · rw [u13.gpr, dpVal, u12.other .r4 (by decide), u11.other .r4 (by decide), u10.gpr, dpVal,
      u9.other .r12 (by decide), u8.gpr, u9.other .r4 (by decide), u8.other .r4 (by decide),
      u7.other .r4 (by decide), good6, u12.gpr, dpVal, u11.gpr, u11.other .r3 (by decide),
      u10.other .r3 (by decide), u9.other .r3 (by decide), u8.other .r3 (by decide), u7.other .r3 (by decide), eq6]
    cases accepted <;> cases equal <;> rfl
  · exact u13.mem.trans (u12.mem.trans (u11.mem.trans (u10.mem.trans (u9.mem.trans (u8.mem.trans
      (u7.mem.trans (u6.mem.trans (u5.mem.trans (u4.mem.trans (u3.mem.trans (u2.mem.trans u1.mem)))))))))))
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
      ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans ((u6.rest (by simp)).trans ((u7.rest (by simp)).trans
      ((u8.rest (by simp)).trans ((u9.rest (by simp)).trans ((u10.rest (by simp)).trans
      ((u11.rest (by simp)).trans ((u12.rest (by simp)).trans (u13.rest (by simp)))))))))))))
end VG.Proof.Rsa.Arm
