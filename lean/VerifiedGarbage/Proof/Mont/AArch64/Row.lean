import VerifiedGarbage.Proof.Mont.AArch64.Words
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# Montgomery arithmetic on AArch64: rows of multiply-accumulate steps

`mulStep t c a b` adds `a · b` and the carry word `c` to `t`, the high word
going to `c` (`mulStep_ok`, by `Word64.multiply_accumulate`), and
`mulSteps ts d` adds `x1 · [d]` (as many words as `ts`) to the words `ts`,
with the carry word `x5` in and out (`mulSteps_ok`), by induction over the
words.
-/

namespace VG.Proof.Mont.AArch64

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Ed25519 (Word64.multiply_accumulate Word64.addCarry Word64.carryOut)

/-- Registers the arithmetic can use for words: distinct, and none of the
registers it uses otherwise (`x0`–`x7`, `x16`, `x17`). -/
def Fresh (ts : List Reg) : Prop :=
  ts.Nodup ∧ ∀ t ∈ ts, t ∉ [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17]

theorem Fresh.tail {t : Reg} {ts : List Reg} (h : Fresh (t :: ts)) : Fresh ts :=
  ⟨(List.nodup_cons.mp h.1).2, fun q hq => h.2 q (List.mem_cons_of_mem _ hq)⟩

theorem Fresh.head {t : Reg} {ts : List Reg} (h : Fresh (t :: ts)) :
    t ∉ ts ∧ t ∉ [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17] :=
  ⟨(List.nodup_cons.mp h.1).1, h.2 t (List.mem_cons_self ..)⟩

/-- Closes `∀ r ∈ rs, r ∈ rs'` for literal lists of registers and variables. -/
macro "sub_regs" : tactic => `(tactic| (intro q hq; simp only [List.mem_cons, List.mem_append,
  List.mem_singleton, List.not_mem_nil, or_false] at hq ⊢; grind))

/-- `t + 2⁶⁴ c = t + c + a b`, through `x3` and `x4`, with `x7 = 0`. -/
theorem mulStep_ok (s : State) {t c a b : Reg} (hz : s.gpr .x7 = 0)
    (ht3 : t ≠ .x3) (ht4 : t ≠ .x4) (ht7 : t ≠ .x7) (hc3 : c ≠ .x3) (hc4 : c ≠ .x4)
    (ha3 : a ≠ .x3) (hb3 : b ≠ .x3) (htc : t ≠ c) :
    WP isa (.block (mulStep t c a b)) s fun s' =>
      (s'.gpr t).toNat + 2 ^ 64 * (s'.gpr c).toNat =
        (s.gpr t).toNat + (s.gpr c).toNat + (s.gpr a).toNat * (s.gpr b).toNat ∧
      Keeps [t, c, .x3, .x4] s s' := by
  apply WP.of_runBlock
  simp only [mulStep, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    ht3, ht4, hc3, hc4, ha3, hb3, htc, Ne.symm htc, Ne.symm ht4, Ne.symm ht7,
    
    hz, Bool.toNat_false, Nat.add_zero, BitVec.add_zero,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · simpa only [Word64.addCarry, Word64.carryOut, Bool.toNat_false,
      Nat.add_zero, BitVec.add_zero] using
      Word64.multiply_accumulate (s.gpr a) (s.gpr b) (s.gpr c) (s.gpr t)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2, ite_false]

/-- A row: `ts + 2^(64 |ts|) x5 = ts + x5 + x1 · [d]`, with `x7 = 0`. -/
theorem mulSteps_ok {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {d : Nat},
    Scr s base size → d + 8 * ts.length ≤ size → d % 8 = 0 → s.gpr .x7 = 0 → Fresh ts →
    WP isa (.block (mulSteps ts d)) s fun s' =>
      regsVal s' ts + 2 ^ (64 * ts.length) * (s'.gpr .x5).toNat =
        regsVal s ts + (s.gpr .x5).toNat + (s.gpr .x1).toNat * wordsVal s.mem base d ts.length ∧
      Keeps (.x5 :: .x2 :: .x3 :: .x4 :: ts) s s'
  | [], s, _, _, _, _, _, _, _ => WP.block_nil ⟨by simp [regsVal, wordsVal],
      fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, d, hs, hd, ha, hz, hf => by
    obtain ⟨htn, hto⟩ := hf.head
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hto
    obtain ⟨ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht16, ht17⟩ := hto
    rw [mulSteps, WP.block_append_iff, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (ld_ok hs (d := d) (by simp at hd; omega) ha .x2) fun s₀ ⟨l₀, k₀, _⟩ => ?_
    have hz₀ : s₀.gpr .x7 = 0 := by rw [k₀.gpr _ (by decide), hz]
    refine WP.mono (mulStep_ok s₀ (t := t) (c := .x5) (a := .x1) (b := .x2) hz₀ ht3 ht4 ht7
      (by decide) (by decide) (by decide) (by decide) ht5) fun s₁ ⟨e₁, k₁⟩ => ?_
    have k₀₁ := (k₀.mono (show ∀ r ∈ [Reg.x2], r ∈ [t, .x5, .x2, .x3, .x4] by sub_regs)).trans
      (k₁.mono (show ∀ r ∈ [t, Reg.x5, .x3, .x4], r ∈ [t, .x5, .x2, .x3, .x4] by sub_regs))
    have hs₁ := hs.of_keeps k₀₁ (by simp [Ne.symm ht0])
    have hz₁ : s₁.gpr .x7 = 0 := by rw [k₀₁.gpr _ (by simp [Ne.symm ht7]), hz]
    refine WP.mono (mulSteps_ok ts hs₁ (d := d + 8) (by simp at hd; omega) (by omega) hz₁ hf.tail)
      fun s₂ ⟨e₂, k₂⟩ => ?_
    have g₂ : ∀ r, r ∉ Reg.x5 :: Reg.x2 :: Reg.x3 :: Reg.x4 :: ts → s₂.gpr r = s₁.gpr r := k₂.1
    have ht₂ : s₂.gpr t = s₁.gpr t := g₂ t (by simp [htn, ht5, ht2, ht3, ht4])
    have hc₁ : s₁.gpr .x1 = s.gpr .x1 := k₀₁.gpr .x1 (by simp [Ne.symm ht1])
    have hc₀ : s₀.gpr .x1 = s.gpr .x1 := k₀.gpr .x1 (by decide)
    have hR₁ : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₀₁.gpr q (by
      have := hf.tail.2 q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
      exact ⟨fun h => htn (h ▸ hq), this.2.2.2.2.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1⟩)
    have hm₁ : s₁.mem = s.mem := k₀₁.mem
    have hm₀ : s₀.mem = s.mem := k₀.mem
    have h5₀ : s₀.gpr .x5 = s.gpr .x5 := k₀.gpr .x5 (by decide)
    have ht₀ : s₀.gpr t = s.gpr t := k₀.gpr t (by simpa using ht2)
    rw [hm₁] at e₂
    rw [l₀, hc₀, h5₀, ht₀] at e₁
    refine ⟨?_, ?_⟩
    · rw [hR₁, hc₁] at e₂
      simp only [regsVal, wordsVal, List.length_cons, pow64_succ, ht₂]
      have h1 : (s.gpr .x1).toNat * ((word s.mem base d).toNat + 2 ^ 64 * wordsVal s.mem base (d + 8)
          ts.length) = (s.gpr .x1).toNat * (word s.mem base d).toNat +
          2 ^ 64 * ((s.gpr .x1).toNat * wordsVal s.mem base (d + 8) ts.length) := by
        rw [Nat.mul_add, Nat.mul_left_comm]
      have h2 : 2 ^ 64 * 2 ^ (64 * ts.length) * (s₂.gpr .x5).toNat =
          2 ^ 64 * (2 ^ (64 * ts.length) * (s₂.gpr .x5).toNat) := Nat.mul_assoc _ _ _
      rw [h1, h2]
      omega
    · exact (k₀₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))

end VG.Proof.Mont.AArch64
