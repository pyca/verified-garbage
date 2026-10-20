module

public import VerifiedGarbage.Impl.Bignum.Arm.Mul64
public import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import VerifiedGarbage.Proof.Bignum.Arm.Mul64Math
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Instruction-level register-pair multiplication -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_mul wp_dp op2_reg dpVal)

theorem mul64Cross_ok (s : State) :
    WP isa (.block mul64Cross) s fun t =>
      t.gpr .r4 = s.gpr .r4 + s.gpr .r1 * s.gpr .r11 + s.gpr .r2 * s.gpr .r10 ∧
      t.mem = s.mem ∧ Rest [.r4, .r5, .r6] s t := by
  unfold mul64Cross
  refine wp_mul fun s1 u1 => ?_
  refine wp_mul fun s2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  refine wp_dp (op2_reg _ _) fun t u4 => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [u4.gpr, dpVal, u3.gpr, dpVal, u3.other .r6 (by decide), u2.gpr,
      u2.other .r4 (by decide), u2.other .r5 (by decide), u1.gpr,
      u1.other .r4 (by decide), u1.other .r2 (by decide), u1.other .r10 (by decide)]
  · rw [u4.mem, u3.mem, u2.mem, u1.mem]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans
      ((u3.rest (by simp)).trans (u4.rest (by simp))))

theorem mul64_ok (s : State) :
    WP isa (.block mul64) s fun t =>
      (t.gpr .r4 ++ t.gpr .r3) = (s.gpr .r10 ++ s.gpr .r1) * (s.gpr .r11 ++ s.gpr .r2) ∧
      t.mem = s.mem ∧ Rest clobbers s t := by
  rw [mul64, WP.block_append_iff]
  refine WP.mono (wideMul_ok s) ?_
  rintro u ⟨product, kept⟩
  refine WP.mono (mul64Cross_ok u) ?_
  rintro t ⟨value, mem, rest⟩
  refine ⟨?_, mem.trans kept.mem, ?_⟩
  · rw [value, rest.gpr .r3 (by simp), kept.regs .r1 (by simp [clobbers]),
      kept.regs .r2 (by simp [clobbers]), kept.regs .r10 (by simp [clobbers]),
      kept.regs .r11 (by simp [clobbers])]
    exact mul64_value _ _ _ _ _ _ product
  · exact (show Rest clobbers s u from ⟨kept.regs, kept.rd, kept.wr, kept.sp⟩).trans
      (rest.mono (by simp [clobbers]))

end VG.Proof.Bignum.Arm
