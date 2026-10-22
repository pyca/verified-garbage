module

public import VerifiedGarbage.Impl.Mont.ArmPacked
public import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Full-word products with the curve kernel's register allocation. -/

@[expose] public section
namespace VG.Proof.Mont.Arm.Packed
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Mont.Arm.Packed
open VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_mov wp_mul op2_reg op2_lsl op2_lsr toNat_shl toNat_shr toNat_mul_lt)

 theorem low_half (x : BitVec 32) : ((x <<< 16) >>> 16).toNat = x.toNat % 65536 := by
  rw [toNat_shr, toNat_shl]
  have := x.isLt
  omega

 theorem cross_ok (s : State) (r : Reg) (h5 : r ≠ .r5)
    (h : (s.gpr .r5).toNat + (s.gpr .r6).toNat * 2 ^ 32 + (s.gpr r).toNat * 2 ^ 16 < 2 ^ 64) :
    WP isa (.block (cross r)) s fun t =>
      (t.gpr .r5).toNat + (t.gpr .r6).toNat * 2 ^ 32 =
        (s.gpr .r5).toNat + (s.gpr .r6).toNat * 2 ^ 32 + (s.gpr r).toNat * 2 ^ 16 ∧
      MacFrame [.r5, .r6] s t := by
  let f := addFlags s (s.gpr .r5) (s.gpr r <<< 16)
  let t := (f.setReg .r5 (s.gpr .r5 + (s.gpr r <<< 16))).setReg .r6
    (s.gpr .r6 + (s.gpr r >>> 16) +
      (if 2 ^ 32 ≤ (s.gpr .r5).toNat + (s.gpr r <<< 16).toNat then 1 else 0))
  have hsh : (1 ≤ 16 ∧ 16 ≤ 31) = True := by decide
  refine WP.of_runBlock ⟨t, ?_, ?_, ?_⟩
  · simp only [cross, runBlock_cons, exec, Op2.eval, hsh, ↓reduceIte, Option.map_some,
      runStep_some, runBlock_nil, gpr_setReg, reduceCtorEq, c_setReg, h5]
    dsimp only [addFlags]
    simp only [decide_eq_true_eq]
    rfl
  · exact add_cross_value _ _ _ h
  · apply MacFrame.setReg (hr := by simp)
    apply MacFrame.setReg (hr := by simp)
    exact MacFrame.addFlags _ _ _ _

 theorem addWord_ok (s : State) (r : Reg)
    (h : (s.gpr .r5).toNat + (s.gpr .r6).toNat * 2 ^ 32 + (s.gpr r).toNat < 2 ^ 64) :
    WP isa (.block (addWord r)) s fun t =>
      (t.gpr .r5).toNat + (t.gpr .r6).toNat * 2 ^ 32 =
        (s.gpr .r5).toNat + (s.gpr .r6).toNat * 2 ^ 32 + (s.gpr r).toNat ∧
      MacFrame [.r5, .r6] s t := by
  let f := addFlags s (s.gpr .r5) (s.gpr r)
  let t := (f.setReg .r5 (s.gpr .r5 + s.gpr r)).setReg .r6
    (s.gpr .r6 + (if 2 ^ 32 ≤ (s.gpr .r5).toNat + (s.gpr r).toNat then 1 else 0))
  refine WP.of_runBlock ⟨t, ?_, ?_, ?_⟩
  · simp only [addWord, runBlock_cons, exec, Op2.eval, Option.map_some,
      show encodable (0 : BitVec 32) = true from rfl, ↓reduceIte, runStep_some, runBlock_nil,
      gpr_setReg, reduceCtorEq, c_setReg]
    dsimp only [addFlags]
    have hz (x : BitVec 32) : x + (0 : BitVec 32) = x := BitVec.add_zero x
    simp only [decide_eq_true_eq, hz]
    rfl
  · exact add_word_value _ _ _ h
  · apply MacFrame.setReg (hr := by simp)
    apply MacFrame.setReg (hr := by simp)
    exact MacFrame.addFlags _ _ _ _

 theorem head_ok (s : State) :
    WP isa (.block head) s fun t =>
      t.gpr .r5 = s.gpr .r2 * ((s.gpr .r7 <<< 16) >>> 16) ∧
      t.gpr .r6 = s.gpr .r0 * (s.gpr .r7 >>> 16) ∧
      t.gpr .r7 = s.gpr .r0 * ((s.gpr .r7 <<< 16) >>> 16) ∧
      t.gpr .r8 = s.gpr .r7 >>> 16 ∧ MacFrame [.r5, .r6, .r7, .r8] s t := by
  apply WP.of_runBlock
  simp only [head, runBlock_cons, isa, exec, Op2.eval, show 1 ≤ 16 ∧ 16 ≤ 31 by decide]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, ?_⟩
  repeat first
    | apply MacFrame.setReg (hr := by simp)
    | exact (Preserves.refl _ _).macFrame


 theorem frame_rest {rs : List Reg} {s t : State} (h : MacFrame rs s t) : Rest rs s t :=
  ⟨h.regs, h.rd, h.wr, h.sp⟩

 theorem product_ok (s : State) (x : BitVec 32)
    (lo : (s.gpr .r2).toNat = x.toNat % 65536) (hi : (s.gpr .r0).toNat = x.toNat / 65536) :
    WP isa (.block product) s fun t =>
      (t.gpr .r5).toNat + (t.gpr .r6).toNat * 2 ^ 32 = x.toNat * (s.gpr .r7).toNat ∧
      Rest [.r5, .r6, .r7, .r8] s t ∧ t.mem = s.mem := by
  rw [product, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (head_ok s) fun s1 ⟨p00, p11, p10, b1, f1⟩ => ?_
  let y := s.gpr .r7
  have hx := x.isLt
  have hy := y.isLt
  have lt (a b : Nat) (ha : a < 65536) (hb : b < 65536) : a * b < 2 ^ 32 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) (by omega)) (by decide)
  have v00 : (s1.gpr .r5).toNat = x.toNat % 65536 * (y.toNat % 65536) := by
    rw [p00, toNat_mul_lt, lo, low_half]
    apply lt <;> (first | rw [lo] | rw [low_half]) <;> omega
  have v11 : (s1.gpr .r6).toNat = x.toNat / 65536 * (y.toNat / 65536) := by
    rw [p11, toNat_mul_lt, hi, toNat_shr]
    apply lt <;> (first | rw [hi] | rw [toNat_shr]) <;> omega
  have v10 : (s1.gpr .r7).toNat = x.toNat / 65536 * (y.toNat % 65536) := by
    rw [p10, toNat_mul_lt, hi, low_half]
    apply lt <;> (first | rw [hi] | rw [low_half]) <;> omega
  have total := partials_value x y
  have bound : x.toNat * y.toNat < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_of_lt hy) (by omega)) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (cross_ok s1 .r7 (by decide) (by rw [v00, v11, v10]; omega)) fun s2 ⟨v2, f2⟩ => ?_
  rw [WP.block_append_iff]
  refine wp_mul fun s3 u3 => WP.block_nil ?_
  have v01 : (s3.gpr .r8).toNat = x.toNat % 65536 * (y.toNat / 65536) := by
    rw [u3.gpr, f2.regs .r2 (by simp), f1.regs .r2 (by simp),
      f2.regs .r8 (by simp), b1, toNat_mul_lt, lo, toNat_shr]
    apply lt <;> (first | rw [lo] | rw [toNat_shr]) <;> omega
  have v3 : (s3.gpr .r5).toNat + (s3.gpr .r6).toNat * 2 ^ 32 =
      x.toNat % 65536 * (y.toNat % 65536) +
      x.toNat / 65536 * (y.toNat / 65536) * 2 ^ 32 + x.toNat / 65536 * (y.toNat % 65536) * 2 ^ 16 := by
    rw [u3.other .r5 (by decide), u3.other .r6 (by decide), v2, v00, v11, v10]
  refine WP.mono (cross_ok s3 .r8 (by decide) (by rw [v3, v01]; omega)) fun t ⟨v4, f4⟩ => ?_
  refine ⟨?_, (frame_rest f1).trans ((frame_rest f2).mono (by simp) |>.trans
    ((u3.rest (by simp)).trans ((frame_rest f4).mono (by simp)))), ?_⟩
  · rw [v4, v3, v01]; exact total
  · rw [f4.mem, u3.mem, f2.mem, f1.mem]

end VG.Proof.Mont.Arm.Packed
