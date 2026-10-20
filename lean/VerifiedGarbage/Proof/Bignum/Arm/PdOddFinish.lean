module

public import VerifiedGarbage.Impl.Bignum.Arm.PdChecks
public import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! # Combine the public comparison and parity bits into one branch condition -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_dp wp_subs op2_imm op2_reg dpVal)

theorem pdOddFinish_ok (s : State) :
    WP isa (.block pdOddFinish) s fun t =>
      t.gpr .r11 = s.gpr .r11 &&& (s.gpr .r1 &&& 1) ∧
      t.z = ((s.gpr .r11 &&& (s.gpr .r1 &&& 1)) == 0) ∧
      t.mem = s.mem ∧ Rest [.r1, .r11] s t := by
  unfold pdOddFinish
  refine wp_dp (op2_imm (by decide)) fun u a => ?_
  refine wp_dp (op2_reg _ _) fun v b => ?_
  refine wp_subs (op2_imm (by decide)) fun t c zero => WP.block_nil ?_
  have value : v.gpr .r11 = s.gpr .r11 &&& (s.gpr .r1 &&& 1) := by
    rw [b.gpr, dpVal, a.other .r11 (by decide), a.gpr, dpVal]
  have subzero : v.gpr .r11 - (0 : BitVec 32) = v.gpr .r11 := BitVec.sub_zero _
  exact ⟨by rw [c.gpr, subzero, value], by rw [zero, subzero, value],
    c.mem.trans (b.mem.trans a.mem),
    (a.rest (by simp)).trans ((b.rest (by simp)).trans (c.rest (by simp)))⟩

end VG.Proof.Bignum.Arm
