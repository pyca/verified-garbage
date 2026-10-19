module

public import VerifiedGarbage.Impl.Bignum.Arm.Sub
public import VerifiedGarbage.Proof.Bignum.Arm.Mac
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Exact subtraction and borrow on ARMv7 -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm

theorem MacFrame.subFlags (rs : List Reg) (s : State) (x y : BitVec 32) :
    MacFrame rs s (subFlags s x y) := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Capturing and inverting the ARM carry flag gives the subtraction borrow. -/
theorem subWord_ok (s : State) (d borrow a b : Reg) (hd : d ≠ borrow) :
    WP isa (.block (subWord d borrow a b)) s fun t =>
      t.gpr d = s.gpr a - s.gpr b ∧
      t.gpr borrow = (if (s.gpr b).toNat ≤ (s.gpr a).toNat then 0 else 1) ∧
      MacFrame [d, borrow] s t := by
  apply WP.of_runBlock
  simp only [subWord, runBlock_cons, runStep_some, exec, Op2.eval,
    Option.map_some, show encodable (0 : BitVec 32) = true from rfl,
    show encodable (1 : BitVec 32) = true from rfl, ↓reduceIte,
    gpr_setReg_self, c_setReg]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp only [gpr_setReg_of_ne _ _ hd, gpr_setReg_self]
  · rw [gpr_setReg_self]
    change ((0 : BitVec 32) + 0 +
      (if (subFlags s (s.gpr a) (s.gpr b)).c then 1 else 0)) ^^^ 1 = _
    dsimp only [subFlags]
    by_cases h : (s.gpr b).toNat ≤ (s.gpr a).toNat <;> simp only [h, decide_true,
      decide_false, Bool.false_eq_true, ite_true, ite_false] <;> rfl
  · repeat first
      | apply MacFrame.setReg (hr := by simp)
      | exact MacFrame.subFlags _ _ _ _

/-- The word and borrow together represent the exact integer difference. -/
theorem subWord_value (s : State) (d borrow a b : Reg) (hd : d ≠ borrow) :
    WP isa (.block (subWord d borrow a b)) s fun t =>
      (t.gpr d).toNat + (s.gpr b).toNat =
        (s.gpr a).toNat + 2 ^ 32 * (t.gpr borrow).toNat ∧
      (t.gpr borrow).toNat ≤ 1 ∧ MacFrame [d, borrow] s t := by
  refine WP.mono (subWord_ok s d borrow a b hd) ?_
  rintro t ⟨diff, borrow, keep⟩
  refine ⟨?_, ?_, keep⟩
  · rw [diff, borrow]
    have ha := (s.gpr a).isLt
    have hb := (s.gpr b).isLt
    split <;> simp only [BitVec.toNat_sub, show (0 : BitVec 32).toNat = 0 from rfl,
      show (1 : BitVec 32).toNat = 1 from rfl] <;> omega
  · rw [borrow]
    split <;> decide

/-- A two-stage subtraction propagates a one-bit borrow without overflow. -/
theorem subBorrow_ok (s : State) (hc : (s.gpr .r11).toNat ≤ 1) :
    WP isa (.block subBorrow) s fun t =>
      (t.gpr .r3).toNat + (s.gpr .r2).toNat + (s.gpr .r11).toNat =
        (s.gpr .r1).toNat + 2 ^ 32 * (t.gpr .r11).toNat ∧
      (t.gpr .r11).toNat ≤ 1 ∧ MacFrame [.r3, .r4, .r5, .r11] s t := by
  rw [subBorrow, List.append_assoc]
  apply WP.block_append_iff.mpr
  refine WP.mono (subWord_value s .r3 .r4 .r1 .r2 (by decide)) ?_
  rintro s1 ⟨v1, b1, k1⟩
  apply WP.block_append_iff.mpr
  refine WP.mono (subWord_value s1 .r3 .r5 .r3 .r11 (by decide)) ?_
  rintro s2 ⟨v2, b2, k2⟩
  have c1 : s1.gpr .r11 = s.gpr .r11 := k1.regs .r11 (by simp)
  have c2 : s2.gpr .r4 = s1.gpr .r4 := k2.regs .r4 (by simp)
  have ha := (s.gpr .r1).isLt
  have hb := (s.gpr .r2).isLt
  have hd := (s2.gpr .r3).isLt
  have hsum : (s2.gpr .r4).toNat + (s2.gpr .r5).toNat ≤ 1 := by
    rw [c1] at v2
    rw [c2]
    omega
  have value : (s2.gpr .r3).toNat + (s.gpr .r2).toNat + (s.gpr .r11).toNat =
      (s.gpr .r1).toNat + 2 ^ 32 * ((s2.gpr .r4).toNat + (s2.gpr .r5).toNat) := by
    rw [c1] at v2
    rw [c2, Nat.mul_add]
    omega
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, exec, Op2.eval, Option.map_some]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, BitVec.toNat_add]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact value
  · simp only [gpr_setReg_self, BitVec.toNat_add]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hsum
  · apply MacFrame.setReg (hr := by simp)
    exact (k1.mono (by simp_all)).trans (k2.mono (by simp_all))

theorem subBorrow_ct : ConstantTime isa (fun _ => True) (fun _ _ => True) (.block subBorrow) := by
  refine ConstantTime.of_silent fun s tr t _ h => ?_
  rw [Exec.block_iff] at h
  cases h
  rfl

end VG.Proof.Bignum.Arm
