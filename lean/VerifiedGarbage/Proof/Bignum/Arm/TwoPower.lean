module

public import VerifiedGarbage.Impl.Bignum.Arm.TwoPower
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Exp4
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

/-! RSA's five masked shifts construct the full power-of-two metadata
word for any native t. No memory or control-flow branch depends on t. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.TwoPower
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Proof.RsaKeyGen.Arm.Cand (powStep_ok pw)

theorem code_ok (s : State) :
    WP isa (.block VG.Impl.Bignum.Arm.TwoPower.code) s fun t =>
      (t.gpr .r2).toNat + 2 ^ 32 * (t.gpr .r3).toNat = 2 ^ ((s.gpr .r1).toNat % 64) ∧
        t.mem = s.mem ∧ Rest [.r1, .r2, .r3, .r4] s t := by
  unfold VG.Impl.Bignum.Arm.TwoPower.code
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_dp (op2_imm (by decide)) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have x2 : s2.gpr .r1 = s.gpr .r1 &&& 63 := by rw [u2.other _ (by decide), u1.gpr, dpVal]
  refine powStep_ok (by decide) x2 u2.gpr fun s3 k3 m3 x3 y3 => ?_
  refine powStep_ok (by decide) x3 y3 fun s4 k4 m4 x4 y4 => ?_
  refine powStep_ok (by decide) x4 y4 fun s5 k5 m5 x5 y5 => ?_
  refine powStep_ok (by decide) x5 y5 fun s6 k6 m6 x6 y6 => ?_
  refine powStep_ok (by decide) x6 y6 fun s7 k7 m7 x7 y7 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s8 u8 => wp_dp (op2_imm (by decide)) fun s9 u9 =>
    wp_mov (op2_imm (by decide)) fun s10 u10 => wp_dp (op2_reg _ _) fun s11 u11 =>
    wp_dp (op2_reg _ _) fun s12 u12 => wp_dp (op2_reg _ _) fun s13 u13 => WP.block_nil ?_
  have highBit : s9.gpr .r3 = (s.gpr .r1 &&& 63) >>> 5 &&& 1 := by
    rw [u9.gpr, dpVal, u8.gpr, x7]
  have high12 : s12.gpr .r3 = (pw (s.gpr .r1)).2 := by
    rw [u12.gpr, dpVal, u11.gpr, dpVal, u10.gpr, u10.other _ (by decide), highBit,
      u11.other _ (by decide), u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), y7]
    rfl
  have low13 : s13.gpr .r2 = (pw (s.gpr .r1)).1 := by
    rw [u13.gpr, dpVal, u12.other _ (by decide), u11.other _ (by decide), u10.other _ (by decide),
      u9.other _ (by decide), u8.other _ (by decide), y7, high12]
    rfl
  have high13 : s13.gpr .r3 = (pw (s.gpr .r1)).2 := by rw [u13.other _ (by decide), high12]
  refine ⟨?_, ?_, ?_⟩
  · rw [low13, high13]
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using VG.Proof.RsaKeyGen.Arm.Cand.pw_val (s.gpr .r1).toNat
  · rw [u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, m7, m6, m5, m4, m3, u2.mem, u1.mem]
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans
      (((k3.trans (k4.trans (k5.trans (k6.trans k7)))).mono (by decide)).trans
        ((u8.rest (by decide)).trans ((u9.rest (by decide)).trans ((u10.rest (by decide)).trans
          ((u11.rest (by decide)).trans ((u12.rest (by decide)).trans (u13.rest (by decide)))))))))

theorem code_word_ok (s : State) :
    WP isa (.block VG.Impl.Bignum.Arm.TwoPower.code) s fun t =>
      (t.gpr .r3 ++ t.gpr .r2 : BitVec 64) = BitVec.twoPow 64 ((s.gpr .r1).toNat % 64) ∧
        t.mem = s.mem ∧ Rest [.r1, .r2, .r3, .r4] s t := by
  refine WP.mono (code_ok s) ?_
  rintro t ⟨value, memory, rest⟩
  refine ⟨?_, memory, rest⟩
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (t.gpr .r2).isLt,
    Nat.shiftLeft_eq, BitVec.toNat_twoPow_of_lt (Nat.mod_lt _ (by decide : 0 < 64))]
  omega

end VG.Proof.Bignum.Arm.TwoPower
