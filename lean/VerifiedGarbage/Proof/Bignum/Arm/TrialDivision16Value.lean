module

public import VerifiedGarbage.Impl.Bignum.Arm.TrialDivision16
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Exact public-value propagation through the RSA/FFDH small-prime reducer. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.TrialDivision16
open VG VG.Arm VG.Proof.X25519.Arm

def redcWord (digit acc inverse divisor : BitVec 32) : BitVec 32 :=
  (((((digit + acc) * inverse) <<< 16) >>> 16) * divisor + (digit + acc)) >>> 16

theorem redcWord_ok (s : State) :
    WP isa (.block VG.Impl.Bignum.Arm.TrialDivision16.redc) s fun t =>
      (t.gpr .r2 = redcWord (s.gpr .r5) (s.gpr .r2) (s.gpr .r4) (s.gpr .r3) ∧ t.mem = s.mem) ∧
      Rest [.r2, .r5, .r6] s t := by
  unfold VG.Impl.Bignum.Arm.TrialDivision16.redc
  refine wp_dp (op2_reg _ _) fun u1 v1 => wp_mul fun u2 v2 => wp_mov (op2_lsl (by decide)) fun u3 v3 =>
    wp_mov (op2_lsr (by decide)) fun u4 v4 => wp_mul fun u5 v5 => wp_dp (op2_reg _ _) fun u6 v6 =>
      wp_mov (op2_lsr (by decide)) fun t v7 => WP.block_nil ?_
  refine ⟨⟨?_, by rw [v7.mem, v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]⟩,
    (v1.rest (by simp)).trans ((v2.rest (by simp)).trans ((v3.rest (by simp)).trans
      ((v4.rest (by simp)).trans ((v5.rest (by simp)).trans ((v6.rest (by simp)).trans (v7.rest (by simp)))))))⟩
  rw [v7.gpr, v6.gpr, dpVal, v5.gpr, v4.gpr, v3.gpr, v2.gpr, v1.gpr, dpVal,
    v5.other .r5 (by decide), v4.other .r5 (by decide),
    v3.other .r5 (by decide), v2.other .r5 (by decide), v1.gpr, dpVal,
    v4.other .r3 (by decide), v3.other .r3 (by decide), v2.other .r3 (by decide), v1.other .r3 (by decide),
    v1.other .r4 (by decide)]
  rfl

end VG.Proof.Bignum.Arm.TrialDivision16
