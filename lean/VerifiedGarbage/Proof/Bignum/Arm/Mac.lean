module

public import VerifiedGarbage.Impl.Bignum.Arm.Mac
public import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The exact multiply-accumulate value and its carry, on ARMv7 -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm

/-- A multiply-accumulate of four full words fits in two words. -/
theorem mac_bound (a b acc carry : BitVec 32) :
    a.toNat * b.toNat + acc.toNat + carry.toNat < 2 ^ 64 := by
  have ha := a.isLt
  have hb := b.isLt
  have ht := acc.isLt
  have hc := carry.isLt
  have := Nat.mul_le_mul (show a.toNat ≤ 2 ^ 32 - 1 by omega)
    (show b.toNat ≤ 2 ^ 32 - 1 by omega)
  omega

/-- The high word receives precisely the low word's addition carry. -/
theorem add_word_value (lo hi x : BitVec 32)
    (h : lo.toNat + hi.toNat * 2 ^ 32 + x.toNat < 2 ^ 64) :
    (lo + x).toNat +
      (hi + (if 2 ^ 32 ≤ lo.toNat + x.toNat then 1 else 0 : BitVec 32)).toNat * 2 ^ 32 =
      lo.toNat + hi.toNat * 2 ^ 32 + x.toNat := by
  have hl := lo.isLt
  have hh := hi.isLt
  have hx := x.isLt
  by_cases hc : 2 ^ 32 ≤ lo.toNat + x.toNat
  · simp only [hc, ite_true, BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  · simp only [hc, ite_false, BitVec.toNat_add, show (0 : BitVec 32).toNat = 0 from rfl]
    omega

/-- Preservation apart from the explicitly listed registers and flags. -/
structure MacFrame (rs : List Reg) (s t : State) : Prop where
  regs : ∀ r, r ∉ rs → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  unknowns : t.unknowns = s.unknowns
  syms : t.syms = s.syms

theorem Preserves.macFrame {rs : List Reg} {s t : State} (h : Preserves rs s t) : MacFrame rs s t :=
  ⟨h.regs, h.mem, h.sp, h.rd, h.wr, h.unknowns, h.syms⟩

theorem MacFrame.setReg {rs : List Reg} {s t : State} (h : MacFrame rs s t)
    {r : Reg} (hr : r ∈ rs) (x : BitVec 32) : MacFrame rs s (t.setReg r x) := by
  refine ⟨?_, h.mem, h.sp, h.rd, h.wr, h.unknowns, h.syms⟩
  intro q hq
  rw [gpr_setReg_of_ne _ _ (by intro e; exact hq (e ▸ hr))]
  exact h.regs q hq

theorem MacFrame.addFlags (rs : List Reg) (s : State) (x y : BitVec 32) :
    MacFrame rs s (addFlags s x y) := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem MacFrame.trans {rs : List Reg} {s t u : State}
    (h : MacFrame rs s t) (k : MacFrame rs t u) : MacFrame rs s u :=
  ⟨fun r hr => (k.regs r hr).trans (h.regs r hr), k.mem.trans h.mem,
    k.sp.trans h.sp, k.rd.trans h.rd, k.wr.trans h.wr,
    k.unknowns.trans h.unknowns, k.syms.trans h.syms⟩

theorem MacFrame.mono {rs rs' : List Reg} {s t : State}
    (h : MacFrame rs s t) (hr : ∀ r ∈ rs, r ∈ rs') : MacFrame rs' s t :=
  { h with regs := fun r hn => h.regs r (fun hmem => hn (hr r hmem)) }

/-- One addition, with the carry included in the high word. -/
theorem addWord_ok (s : State) (r : Reg)
    (h : (s.gpr .r3).toNat + (s.gpr .r4).toNat * 2 ^ 32 + (s.gpr r).toNat < 2 ^ 64) :
    WP isa (.block (addWord r)) s fun t =>
      (t.gpr .r3).toNat + (t.gpr .r4).toNat * 2 ^ 32 =
        (s.gpr .r3).toNat + (s.gpr .r4).toNat * 2 ^ 32 + (s.gpr r).toNat ∧
      MacFrame [.r3, .r4] s t := by
  let f := addFlags s (s.gpr .r3) (s.gpr r)
  let t := (f.setReg .r3 (s.gpr .r3 + s.gpr r)).setReg .r4
    (s.gpr .r4 + (if 2 ^ 32 ≤ (s.gpr .r3).toNat + (s.gpr r).toNat then 1 else 0))
  refine WP.of_runBlock ⟨t, ?_, ?_, ?_⟩
  · simp only [addWord, runBlock_cons, exec, Op2.eval, Option.map_some,
      show encodable (0 : BitVec 32) = true from rfl, ↓reduceIte, runStep_some, runBlock_nil,
      gpr_setReg, reduceCtorEq, c_setReg]
    dsimp only [addFlags]
    have hz (x : BitVec 32) : x + (0 : BitVec 32) = x := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add]
      change x.toNat % 2 ^ 32 = x.toNat
      exact Nat.mod_eq_of_lt x.isLt
    simp only [decide_eq_true_eq, hz]
    rfl
  · change ((s.gpr .r3 + s.gpr r).toNat +
      (s.gpr .r4 + (if 2 ^ 32 ≤ (s.gpr .r3).toNat + (s.gpr r).toNat then 1 else 0)).toNat * 2 ^ 32 = _)
    exact add_word_value _ _ _ h
  · apply MacFrame.setReg (hr := by simp)
    apply MacFrame.setReg (hr := by simp)
    exact MacFrame.addFlags _ _ _ _


/-- The row step returns the exact product plus accumulator and carry.
Only `r3`–`r9` and the flags change; the input words and pointers survive. -/
theorem mac_ok (s : State) :
    WP isa (.block mac) s fun t =>
      (t.gpr .r3).toNat + (t.gpr .r4).toNat * 2 ^ 32 =
        (s.gpr .r1).toNat * (s.gpr .r2).toNat + (s.gpr .r10).toNat + (s.gpr .r11).toNat ∧
      MacFrame clobbers s t := by
  rw [mac, List.append_assoc]
  apply WP.block_append_iff.mpr
  refine WP.mono (wideMul_ok s) ?_
  rintro s1 ⟨prod, frame1⟩
  have acc1 := frame1.regs .r10 (by simp [clobbers])
  have carry1 := frame1.regs .r11 (by simp [clobbers])
  have hb := mac_bound (s.gpr .r1) (s.gpr .r2) (s.gpr .r10) (s.gpr .r11)
  apply WP.block_append_iff.mpr
  refine WP.mono (addWord_ok s1 .r10 (by rw [prod, acc1]; omega)) ?_
  rintro s2 ⟨sum, frame2⟩
  have carry2 : s2.gpr .r11 = s.gpr .r11 :=
    (frame2.regs .r11 (by simp)).trans carry1
  refine WP.mono (addWord_ok s2 .r11 (by rw [sum, prod, acc1, carry2]; exact hb)) ?_
  rintro s3 ⟨value, frame3⟩
  refine ⟨?_, frame1.macFrame.trans ((frame2.mono ?_).trans (frame3.mono ?_))⟩
  · rw [value, sum, prod, acc1, carry2]
  all_goals intro r hr; cases r <;> simp_all [clobbers]

/-- The multiply-accumulate is a fixed sequence without memory accesses. -/
theorem mac_ct : ConstantTime isa (fun _ => True) (fun _ _ => True) (.block mac) := by
  refine ConstantTime.of_silent fun s tr t _ h => ?_
  rw [Exec.block_iff] at h
  cases h
  rfl

end VG.Proof.Bignum.Arm
