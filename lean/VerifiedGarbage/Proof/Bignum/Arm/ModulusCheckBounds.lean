module

public import VerifiedGarbage.Impl.Bignum.Arm.ModulusCheck
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Sign-bit comparisons for the leading byte and minimum RSA modulus -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_dp wp_mov op2_imm op2_reg op2_lsl op2_lsr dpVal)

theorem modulusCheckBounds_ok (s : State) :
    WP isa (.block modulusCheckBounds) s fun t =>
      t.gpr .r7 = (s.gpr .r1 - 1) >>> 31 ∧
      t.gpr .r9 = ((((s.gpr .r6 - 64) <<< 8) + s.gpr .r1) - 128) >>> 31 ∧
      t.mem = s.mem ∧ Rest [.r7, .r9] s t := by
  unfold modulusCheckBounds
  refine wp_dp (op2_imm (by decide)) fun s1 h1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 h2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 h3 => ?_
  refine wp_mov (op2_lsl (by decide)) fun s4 h4 => ?_
  refine wp_dp (op2_reg _ _) fun s5 h5 => ?_
  refine wp_dp (op2_imm (by decide)) fun s6 h6 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t h7 => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h7.other .r7 (by decide), h6.other .r7 (by decide), h5.other .r7 (by decide),
      h4.other .r7 (by decide), h3.other .r7 (by decide), h2.gpr, h1.gpr, dpVal]
  · rw [h7.gpr, h6.gpr, dpVal, h5.gpr, dpVal, h4.gpr, h3.gpr, dpVal,
      h2.other .r6 (by decide), h1.other .r6 (by decide), h4.other .r1 (by decide),
      h3.other .r1 (by decide), h2.other .r1 (by decide), h1.other .r1 (by decide)]
  · rw [h7.mem, h6.mem, h5.mem, h4.mem, h3.mem, h2.mem, h1.mem]
  · exact (h1.rest (by simp)).trans ((h2.rest (by simp)).trans ((h3.rest (by simp)).trans
      ((h4.rest (by simp)).trans ((h5.rest (by simp)).trans ((h6.rest (by simp)).trans (h7.rest (by simp)))))))

end VG.Proof.Bignum.Arm
