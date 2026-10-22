module

public import VerifiedGarbage.Impl.Bignum.Arm.Sub
public import VerifiedGarbage.Proof.Bignum.Arm.Mac
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Exact subtraction and borrow on ARMv7 -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm

theorem MacFrame.subFlags (rs : List Reg) (s : State) (x y : BitVec 32) :
    MacFrame rs s (subFlags s x y) := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem MacFrame.withSubFlags {rs : List Reg} {s t : State} (h : MacFrame rs s t)
    (x y : BitVec 32) : MacFrame rs s (VG.Arm.subFlags t x y) :=
  h.trans (MacFrame.subFlags rs t x y)

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
  apply WP.of_runBlock
  simp only [subBorrow, runBlock_cons, runStep_some, exec, Op2.eval,
    Option.map_some, show encodable (0 : BitVec 32) = true from rfl,
    show encodable (1 : BitVec 32) = true from rfl,
    show encodable (3 : BitVec 32) = true from rfl, ↓reduceIte,
    gpr_setReg_self, gpr_setReg_of_ne _ _ (by decide : Reg.r3 ≠ .r4),
    gpr_setReg_of_ne _ _ (by decide : Reg.r11 ≠ .r3),
    gpr_setReg_of_ne _ _ (by decide : Reg.r11 ≠ .r4), c_setReg]
  refine ⟨_, rfl, ?value, ?bound, ?frame⟩
  case frame =>
    repeat first
      | apply MacFrame.setReg (hr := by simp)
      | apply MacFrame.withSubFlags
      | exact ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  all_goals
    simp only [gpr_setReg, subFlags, reduceCtorEq, ↓reduceIte]
    have ha := (s.gpr .r1).isLt
    have hb := (s.gpr .r2).isLt
    by_cases h1 : (s.gpr .r2).toNat ≤ (s.gpr .r1).toNat <;>
      by_cases h2 : (s.gpr .r11).toNat ≤ (s.gpr .r1 - s.gpr .r2).toNat <;>
      simp only [h1, h2, decide_true, decide_false, ite_true, ite_false, Bool.false_eq_true] <;>
      dsimp <;> simp only [BitVec.toNat_sub] at h2 ⊢ <;> omega

theorem subBorrow_ct : ConstantTime isa (fun _ => True) (fun _ _ => True) (.block subBorrow) := by
  refine ConstantTime.of_silent fun s tr t _ h => ?_
  rw [Exec.block_iff] at h
  cases h
  rfl

end VG.Proof.Bignum.Arm
