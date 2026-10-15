module

public import VerifiedGarbage.Impl.Bignum.Arm.ShiftLeft
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # One native-word left shift: arithmetic, memory safety and frame -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

theorem shiftLeft_word (x c : BitVec 32) (hc : c.toNat ≤ 1) :
    (x + x + c).toNat + 2 ^ 32 * (x >>> 31).toNat = 2 * x.toNat + c.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight]
  simp only [Nat.shiftRight_eq_div_pow]
  have hx := x.isLt
  omega

theorem shiftLeftStep_ok (s : State) (a : Addr)
    (ha : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = a)
    (wa : InRegions s.wr a 4) (ra : InRegions (s.rd ++ s.wr) a 4)
    (hc : (s.gpr .r11).toNat ≤ 1) :
    WP isa (.block shiftLeftStep) s fun t =>
      (t.gpr .r3).toNat + 2 ^ 32 * (t.gpr .r11).toNat =
        2 * (s.mem.readW a 32).toNat + (s.gpr .r11).toNat ∧
      (t.gpr .r11).toNat ≤ 1 ∧ t.mem = s.mem.writeW a (t.gpr .r3) ∧
      t.gpr .r0 = s.gpr .r0 + 4 ∧ t.gpr .lr = s.gpr .lr - 1 ∧
      t.z = (s.gpr .lr - 1 == 0) ∧ Rest [.r0, .r3, .r4, .r11, .lr] s t := by
  unfold shiftLeftStep
  refine wp_ldr (by decide) ha ra fun s1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  refine wp_dp (op2_reg _ _) fun s4 u4 => ?_
  refine wp_mov (op2_reg _ _) fun s5 u5 => ?_
  have p0 : s5.gpr .r0 = s.gpr .r0 := by
    rw [u5.other .r0 (by decide), u4.other .r0 (by decide), u3.other .r0 (by decide),
      u2.other .r0 (by decide), u1.other .r0 (by decide)]
  refine wp_str (a := a) (by decide) (by rw [p0]; exact ha)
    (by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]; exact wa) fun s6 u6 => ?_
  refine wp_dp (op2_imm (by decide)) fun s7 u7 => ?_
  refine wp_subs (op2_imm (by decide)) fun t u8 hz => WP.block_nil ?_
  have value : t.gpr .r3 = s.mem.readW a 32 + s.mem.readW a 32 + s.gpr .r11 := by
    rw [u8.other .r3 (by decide), u7.other .r3 (by decide), u6.gpr,
      u5.other .r3 (by decide), u4.gpr, dpVal, u3.gpr, dpVal,
      u2.other .r3 (by decide), u1.gpr, u3.other .r11 (by decide),
      u2.other .r11 (by decide), u1.other .r11 (by decide)]
  have carry : t.gpr .r11 = s.mem.readW a 32 >>> 31 := by
    rw [u8.other .r11 (by decide), u7.other .r11 (by decide), u6.gpr, u5.gpr,
      u4.other .r4 (by decide), u3.other .r4 (by decide), u2.gpr, u1.gpr]
  have count : s6.gpr .lr = s.gpr .lr := by
    rw [u6.gpr, u5.other .lr (by decide), u4.other .lr (by decide),
      u3.other .lr (by decide), u2.other .lr (by decide), u1.other .lr (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [value, carry]; exact shiftLeft_word _ _ hc
  · rw [carry, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := (s.mem.readW a 32).isLt
    omega
  · rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    rw [u8.other .r3 (by decide), u7.other .r3 (by decide), u6.gpr]
  · rw [u8.other .r0 (by decide), u7.gpr, dpVal, u6.gpr, p0]
  · rw [u8.gpr, u7.other .lr (by decide), count]
  · rw [hz, u7.other .lr (by decide), count]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans
      ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans
        ((u6.rest _).trans ((u7.rest (by simp)).trans (u8.rest (by simp))))))))

end VG.Proof.Bignum.Arm
