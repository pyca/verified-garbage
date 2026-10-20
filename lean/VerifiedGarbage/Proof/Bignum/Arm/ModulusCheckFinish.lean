module

public import VerifiedGarbage.Impl.Bignum.Arm.ModulusCheck
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Combine RSA modulus rejection bits into the branch condition -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_dp wp_subs op2_imm op2_reg dpVal)

theorem modulusCheckFinish_ok (s : State) :
    WP isa (.block modulusCheckFinish) s fun t =>
      t.z = ((s.gpr .r7 ||| ((s.gpr .r2 &&& 1) ^^^ 1) ||| s.gpr .r9) == 0) ∧
      t.mem = s.mem ∧ Rest [.r2, .r7] s t := by
  unfold modulusCheckFinish
  refine wp_dp (op2_imm (by decide)) fun s1 h1 => ?_
  refine wp_dp (op2_imm (by decide)) fun s2 h2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 h3 => ?_
  refine wp_dp (op2_reg _ _) fun s4 h4 => ?_
  refine wp_subs (op2_imm (by decide)) fun t h5 zero => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · have subzero : s4.gpr .r7 - (0 : BitVec 32) = s4.gpr .r7 := BitVec.sub_zero _
    rw [zero, subzero, h4.gpr, dpVal, h3.gpr, dpVal,
      h2.other .r7 (by decide), h1.other .r7 (by decide), h2.gpr, dpVal, h1.gpr, dpVal,
      h3.other .r9 (by decide), h2.other .r9 (by decide), h1.other .r9 (by decide)]
  · rw [h5.mem, h4.mem, h3.mem, h2.mem, h1.mem]
  · exact (h1.rest (by simp)).trans ((h2.rest (by simp)).trans
      ((h3.rest (by simp)).trans ((h4.rest (by simp)).trans (h5.rest (by simp)))))

end VG.Proof.Bignum.Arm
