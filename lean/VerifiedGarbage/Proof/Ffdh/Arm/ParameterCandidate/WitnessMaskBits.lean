module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.TwoPower
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! Reuse RSA's fixed-step masked shifts for a full native-word witness
mask, including n=32, without shifting a native register by its width. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

theorem witnessMaskBits_ok {s : State} {bits : Nat} (bound : bits ≤ 32)
    (count : s.gpr .r6 = BitVec.ofNat 32 bits) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskBits s fun t =>
      t.gpr .r7 = BitVec.ofNat 32 (2 ^ bits - 1) ∧ t.mem = s.mem ∧
      Rest [.r1, .r2, .r3, .r4, .r7] s t := by
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.witnessMaskBits, WP.seq_iff]
  refine wp_mov (op2_reg _ _) fun u move => WP.block_nil ?_
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.Bignum.Arm.TwoPower.code_ok u) ?_
  rintro v ⟨value, memV, restV⟩
  rw [move.gpr, count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : bits < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : bits < 64)] at value
  have low : v.gpr .r2 = BitVec.ofNat 32 (2 ^ bits) := by
    apply BitVec.eq_of_toNat_eq
    have reduced := congrArg (fun n => n % 2 ^ 32) value
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (v.gpr .r2).isLt] at reduced
    exact reduced
  refine wp_dp (op2_imm (by decide)) fun t subtract => WP.block_nil ?_
  refine ⟨?_, subtract.mem.trans (memV.trans move.mem),
    (move.rest (by simp)).trans ((restV.mono (by simp)).trans (subtract.rest (by simp)))⟩
  rw [subtract.gpr, dpVal, low]
  change BitVec.ofNat 32 (2 ^ bits) - BitVec.ofNat 32 1 = _
  exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (Nat.two_pow_pos bits)

end VG.Proof.Ffdh.Arm.ParameterCandidate
