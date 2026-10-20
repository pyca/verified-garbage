module

public import VerifiedGarbage.Impl.Bignum.Arm.Sub64
import VerifiedGarbage.Proof.Bignum.Arm.Sub64Math
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.Sub
import VerifiedGarbage.Proof.Framework.Block

/-! # Register-pair subtraction and its memory/register frame -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_mov wp_dp op2_reg op2_imm dpVal)

theorem sub64High_ok (s : State) :
    WP isa (.block sub64High) s fun t =>
      t.gpr .r11 = 0 - s.gpr .r4 - s.gpr .r5 ∧ t.mem = s.mem ∧ Rest [.r11] s t := by
  unfold sub64High
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun t u3 => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [u3.gpr, dpVal, u2.gpr, dpVal, u2.other .r5 (by decide),
      u1.gpr, u1.other .r4 (by decide), u1.other .r5 (by decide)]
  · rw [u3.mem, u2.mem, u1.mem]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans (u3.rest (by simp)))

theorem sub64_ok (s : State) :
    WP isa (.block sub64) s fun t =>
      (t.gpr .r11 ++ t.gpr .r2) = ((0 : BitVec 32) ++ s.gpr .r6) - (s.gpr .r4 ++ s.gpr .r3) ∧
      t.mem = s.mem ∧ Rest [.r2, .r5, .r11] s t := by
  rw [sub64, WP.block_append_iff]
  refine WP.mono (subWord_ok s .r2 .r5 .r6 .r3 (by decide)) ?_
  rintro u ⟨low, borrow, kept⟩
  refine WP.mono (sub64High_ok u) ?_
  rintro t ⟨high, mem, rest⟩
  refine ⟨?_, mem.trans kept.mem, ?_⟩
  · rw [high, rest.gpr .r2 (by simp), low, borrow, kept.regs .r4 (by simp)]
    exact sub64_value _ _ _
  · exact (show Rest [.r2, .r5] s u from ⟨kept.regs, kept.rd, kept.wr, kept.sp⟩).mono
      (by simp) |>.trans (rest.mono (by simp))

end VG.Proof.Bignum.Arm
