module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Mont.X86_64.Words
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# Montgomery arithmetic on x86-64: rows of multiply-accumulate steps

`mulSteps ts d` adds `rcx · [d]` (as many words as `ts`) to the words `ts`,
with the carry word `rbp` in and out (`mulSteps_ok`), by induction over the
words, from X25519's multiply-accumulate step.
-/

@[expose] public section

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono mulStep_ok se0 toNat_ofBool)

/-- Registers the arithmetic can use for words: distinct, and none of `rax`,
`rcx`, `rdx`, `rbp` and `rdi`. -/
def Fresh (ts : List Reg) : Prop :=
  ts.Nodup ∧ ∀ t ∈ ts, t ≠ .rax ∧ t ≠ .rcx ∧ t ≠ .rdx ∧ t ≠ .rbp ∧ t ≠ .rdi

theorem Fresh.tail {t : Reg} {ts : List Reg} (h : Fresh (t :: ts)) : Fresh ts :=
  ⟨(List.nodup_cons.mp h.1).2, fun q hq => h.2 q (List.mem_cons_of_mem _ hq)⟩

theorem Fresh.head {t : Reg} {ts : List Reg} (h : Fresh (t :: ts)) :
    t ∉ ts ∧ t ≠ .rax ∧ t ≠ .rcx ∧ t ≠ .rdx ∧ t ≠ .rbp ∧ t ≠ .rdi :=
  ⟨(List.nodup_cons.mp h.1).1, h.2 t (List.mem_cons_self ..)⟩

/-- Registers rows with BMI2 and ADX can use for words: distinct, and none of
`rax`, `rcx`, `rdx` and `rdi` (`rbp` may be one). -/
def FreshX (ts : List Reg) : Prop :=
  ts.Nodup ∧ ∀ t ∈ ts, t ≠ .rax ∧ t ≠ .rcx ∧ t ≠ .rdx ∧ t ≠ .rdi

theorem Fresh.toX {ts : List Reg} (h : Fresh ts) : FreshX ts :=
  ⟨h.1, fun t ht => have := h.2 t ht; ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.2⟩⟩

theorem FreshX.tail {t : Reg} {ts : List Reg} (h : FreshX (t :: ts)) : FreshX ts :=
  ⟨(List.nodup_cons.mp h.1).2, fun q hq => h.2 q (List.mem_cons_of_mem _ hq)⟩

theorem FreshX.head {t : Reg} {ts : List Reg} (h : FreshX (t :: ts)) :
    t ∉ ts ∧ t ≠ .rax ∧ t ≠ .rcx ∧ t ≠ .rdx ∧ t ≠ .rdi :=
  ⟨(List.nodup_cons.mp h.1).1, h.2 t (List.mem_cons_self ..)⟩

/-- Closes `∀ r ∈ rs, r ∈ rs'` for literal lists of registers and variables: by
`decide` for literal registers (most uses, and much cheaper than `grind`),
else by one `simp` on the memberships (each register of `rs` written in
`rs'`, or a variable list of `rs` a part of `rs'`), else by `grind`. -/
tactic_template "sub_regs" : tactic => `(tactic| first
  | decide
  | (simp (config := { contextual := true }) only [List.mem_cons, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false, false_or, forall_eq_or_imp, forall_eq, eq_self_iff_true, true_or, or_true,
      and_true, true_and, and_self, imp_self, implies_true]; done)
  | (intro q hq; simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false]
      at hq ⊢; grind))

theorem mulStep_eq (t c ai : Reg) (src : Src) :
    mulStep t c ai src = Impl.X25519.X86_64.mulStep t c ai src := rfl

/-- A row: `ts + 2^(64 |ts|) rbp = ts + rbp + rcx · [d]`. -/
theorem mulSteps_ok {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {d : Nat},
    Scr s base size → d + 8 * ts.length ≤ size → Fresh ts →
    WP isa (.block (mulSteps ts d)) s fun s' =>
      regsVal s' ts + 2 ^ (64 * ts.length) * (s'.gpr .rbp).toNat =
        regsVal s ts + (s.gpr .rbp).toNat + (s.gpr .rcx).toNat * wordsVal s.mem base d ts.length ∧
      Keeps (.rbp :: .rax :: .rdx :: ts) s s'
  | [], s, _, _, _, _, _ => WP.block_nil ⟨by simp [regsVal, wordsVal],
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, d, hs, hd, hf => by
    obtain ⟨htn, hta, htc, htd, htb, hti⟩ := hf.head
    rw [mulSteps, mulStep_eq, WP.block_append_iff]
    refine WP.mono (mulStep_ok s (readSrc_sc hs (d := d) (by simp at hd; omega_arith)) hta htd
      (by decide) (by decide) (by decide) htb) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by simp [Ne.symm hti])
    refine WP.mono (mulSteps_ok ts hs₁ (d := d + 8) (by simp at hd; omega_arith) hf.tail)
      fun s₂ ⟨e₂, k₂⟩ => ?_
    have g₂ : ∀ r, r ∉ Reg.rbp :: Reg.rax :: Reg.rdx :: ts → s₂.gpr r = s₁.gpr r := k₂.1
    have g₁ : ∀ r, r ∉ [t, Reg.rbp, Reg.rax, Reg.rdx] → s₁.gpr r = s.gpr r := k₁.1
    have ht₂ : s₂.gpr t = s₁.gpr t := g₂ t (by simp [htn, htb, hta, htd])
    have hc₁ : s₁.gpr .rcx = s.gpr .rcx := g₁ .rcx (by simp [Ne.symm htc])
    have hR₁ : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => g₁ q (by
      have := hf.tail.2 q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => htn (h ▸ hq), this.2.2.2.1, this.1, this.2.2.1⟩)
    rw [k₁.2.1] at e₂
    refine ⟨?_, ?_⟩
    · rw [hR₁, hc₁] at e₂
      simp only [regsVal, wordsVal, List.length_cons, pow64_succ, ht₂]
      have h1 : (s.gpr .rcx).toNat * ((word s.mem base d).toNat + 2 ^ 64 * wordsVal s.mem base (d + 8)
          ts.length) = (s.gpr .rcx).toNat * (word s.mem base d).toNat +
          2 ^ 64 * ((s.gpr .rcx).toNat * wordsVal s.mem base (d + 8) ts.length) := by
        rw [Nat.mul_add, Nat.mul_left_comm]
      have h2 : 2 ^ 64 * 2 ^ (64 * ts.length) * (s₂.gpr .rbp).toNat =
          2 ^ 64 * (2 ^ (64 * ts.length) * (s₂.gpr .rbp).toNat) := Nat.mul_assoc _ _ _
      rw [h1, h2]
      have := readSrc_sc hs (d := d) (by simp at hd; omega_arith)
      omega_arith
    · exact (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))

/-- The arithmetic of `mulStepL`: the product's halves, the low half added to
`t`, then the carry word `c`, each carry going into the high half. -/
theorem stepL_arith (a v c t : BitVec 64) :
    let p := a.toNat * v.toNat
    let lo : BitVec 64 := BitVec.ofNat 64 p
    let hi : BitVec 64 := BitVec.ofNat 64 (p / 2 ^ 64)
    let r := t + lo
    let d := hi + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ t.toNat + lo.toNat))).setWidth 64
    (r + c).toNat + 2 ^ 64 *
        (d + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ r.toNat + c.toNat))).setWidth 64).toNat =
      t.toNat + c.toNat + a.toNat * v.toNat := by
  intro p lo hi r d
  have ha := a.isLt; have hv := v.isLt; have hc := c.isLt; have ht := t.isLt
  have hp : p ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  have hlo : lo.toNat = p % 2 ^ 64 := BitVec.toNat_ofNat _ _
  have hhi : hi.toNat = p / 2 ^ 64 := by
    simp only [hi, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega_arith)
  have hdiv : p / 2 ^ 64 ≤ 2 ^ 64 - 2 := by omega_arith
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  simp only [r, d, BitVec.toNat_add, toNat_ofBool, hz, Nat.add_zero, hlo, hhi] at *
  by_cases h1 : 2 ^ 64 ≤ t.toNat + p % 2 ^ 64 <;>
  simp only [h1, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
  [by_cases h2 : 2 ^ 64 ≤ (t.toNat + p % 2 ^ 64) % 2 ^ 64 + c.toNat;
    by_cases h2 : 2 ^ 64 ≤ (t.toNat + p % 2 ^ 64) % 2 ^ 64 + c.toNat] <;>
  simp only [h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

/-- `mulStepL`: `t:c = t + c + ai · src`, as `mulStep_ok`. -/
theorem mulStepL_ok (s : State) {t c ai : Reg} {src : Src} {v : BitVec 64}
    (hsrc : readSrc s src = some v) (ht : t ≠ .rax) (ht' : t ≠ .rdx) (hc : c ≠ .rax)
    (hc' : c ≠ .rdx) (ha : ai ≠ .rax) (htc : t ≠ c) :
    WP isa (.block (mulStepL t c ai src)) s fun s' =>
      (s'.gpr t).toNat + 2 ^ 64 * (s'.gpr c).toNat =
        (s.gpr t).toNat + (s.gpr c).toNat + (s.gpr ai).toNat * v.toNat ∧
      Keeps [t, c, .rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [mulStepL, runBlock_cons, exec, hsrc, Option.map_some, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execMul,
    execAlu, Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, ha, hc, ht, htc, hc', ht',
    Ne.symm htc, Ne.symm ht', ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left', se0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := stepL_arith (s.gpr ai) v (s.gpr c) (s.gpr t)
    simp only at e
    rw [Nat.mul_comm (s.gpr ai).toNat] at e ⊢
    exact e
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2, ite_false]

/-- `mulSteps_ok` for `mulStepsL`. -/
theorem mulStepsL_ok {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {d : Nat},
    Scr s base size → d + 8 * ts.length ≤ size → Fresh ts →
    WP isa (.block (mulStepsL ts d)) s fun s' =>
      regsVal s' ts + 2 ^ (64 * ts.length) * (s'.gpr .rbp).toNat =
        regsVal s ts + (s.gpr .rbp).toNat + (s.gpr .rcx).toNat * wordsVal s.mem base d ts.length ∧
      Keeps (.rbp :: .rax :: .rdx :: ts) s s'
  | [], s, _, _, _, _, _ => WP.block_nil ⟨by simp [regsVal, wordsVal],
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, d, hs, hd, hf => by
    obtain ⟨htn, hta, htc, htd, htb, hti⟩ := hf.head
    rw [mulStepsL, WP.block_append_iff]
    refine WP.mono (mulStepL_ok s (readSrc_sc hs (d := d) (by simp at hd; omega_arith)) hta htd
      (by decide) (by decide) (by decide) htb) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by simp [Ne.symm hti])
    refine WP.mono (mulStepsL_ok ts hs₁ (d := d + 8) (by simp at hd; omega_arith) hf.tail)
      fun s₂ ⟨e₂, k₂⟩ => ?_
    have g₂ : ∀ r, r ∉ Reg.rbp :: Reg.rax :: Reg.rdx :: ts → s₂.gpr r = s₁.gpr r := k₂.1
    have g₁ : ∀ r, r ∉ [t, Reg.rbp, Reg.rax, Reg.rdx] → s₁.gpr r = s.gpr r := k₁.1
    have ht₂ : s₂.gpr t = s₁.gpr t := g₂ t (by simp [htn, htb, hta, htd])
    have hc₁ : s₁.gpr .rcx = s.gpr .rcx := g₁ .rcx (by simp [Ne.symm htc])
    have hR₁ : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => g₁ q (by
      have := hf.tail.2 q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => htn (h ▸ hq), this.2.2.2.1, this.1, this.2.2.1⟩)
    rw [k₁.2.1] at e₂
    refine ⟨?_, ?_⟩
    · rw [hR₁, hc₁] at e₂
      simp only [regsVal, wordsVal, List.length_cons, pow64_succ, ht₂]
      have h1 : (s.gpr .rcx).toNat * ((word s.mem base d).toNat + 2 ^ 64 * wordsVal s.mem base (d + 8)
          ts.length) = (s.gpr .rcx).toNat * (word s.mem base d).toNat +
          2 ^ 64 * ((s.gpr .rcx).toNat * wordsVal s.mem base (d + 8) ts.length) := by
        rw [Nat.mul_add, Nat.mul_left_comm]
      have h2 : 2 ^ 64 * 2 ^ (64 * ts.length) * (s₂.gpr .rbp).toNat =
          2 ^ 64 * (2 ^ (64 * ts.length) * (s₂.gpr .rbp).toNat) := Nat.mul_assoc _ _ _
      rw [h1, h2]
      have := readSrc_sc hs (d := d) (by simp at hd; omega_arith)
      omega_arith
    · exact (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))

end VG.Proof.Mont.X86_64
