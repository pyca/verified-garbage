module

public import VerifiedGarbage.Impl.Rsa.Arm.KeyWs
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Rsa.ZeroTest32
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Normalize a full-word XOR/OR accumulator without branching on its value. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Proof.X25519.Arm

theorem eqNormalize_ok (s : State) :
    WP isa (.block eqNormalize) s fun t =>
      (t.gpr .r1 = (if s.gpr .r2 = 0 then 1 else 0) ∧ t.mem = s.mem) ∧ Rest [.r1] s t := by
  unfold eqNormalize
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun t u5 => WP.block_nil ?_
  refine ⟨⟨?_, u5.mem.trans (u4.mem.trans (u3.mem.trans (u2.mem.trans u1.mem)))⟩,
    (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
      ((u4.rest (by simp)).trans (u5.rest (by simp)))))⟩
  rw [u5.gpr, dpVal, u4.gpr, u3.gpr, dpVal, u2.gpr, dpVal, u1.gpr,
    u2.other .r2 (by decide), u1.other .r2 (by decide), VG.Proof.Rsa.zero_test32]
  by_cases h : s.gpr .r2 = 0
  · simp only [h, decide_true, ite_true]; rfl
  · simp only [h, decide_false, ite_false]; rfl

end VG.Proof.Rsa.Arm.Keys
