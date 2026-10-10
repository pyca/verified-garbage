import VerifiedGarbage.Proof.Weierstrass.AArch64.InvWords
import VerifiedGarbage.Proof.Divstep.Tc

/-!
# Inversion by divsteps on AArch64: the reduction of the coefficients

The carry chains `[d] ± (p & m)` over memory (`chain_ok`), and the reduction
`mredC` of a signed number of `n + 1` words to `mred` (`mredC_ok`).
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Ed25519 (Word64.addCarry Word64.carryOut Word64.addCarry_value)

/-! ## Carry chains -/

/-- `x & m` for a mask `m`, or `x`. -/
def mk : Option Reg → State → Nat → Nat
  | some r, s, x => masked (s.gpr r) x
  | none, _, x => x

/-- The mask register, if any: kept by a chain, and a mask. -/
def MaskOk : Option Reg → State → Prop
  | some r, s => r ∉ [Reg.x0, .x2, .x3] ∧ IsMask (s.gpr r)
  | none, _ => True

theorem mk_le (m : Option Reg) (s : State) (x : Nat) : mk m s x ≤ x := by
  cases m with
  | none => exact Nat.le_refl _
  | some r => simp only [mk, masked]; split <;> omega_arith

theorem mk_add (m : Option Reg) (s : State) (a A b : Nat) : mk m s (a + A * b) = mk m s a + A * mk m s b := by
  cases m with
  | none => rfl
  | some r => exact masked_add _ _ _ _

theorem mk_keep {m : Option Reg} {s s' : State} (hm : MaskOk m s) (h : ∀ r ∉ [Reg.x2, .x3], s'.gpr r = s.gpr r)
    (x : Nat) : mk m s' x = mk m s x := by
  cases m with
  | none => rfl
  | some r =>
    simp only [mk]
    rw [h r fun h' => hm.1 (List.mem_cons_of_mem _ h')]

theorem maskOk_keep {m : Option Reg} {s s' : State} (hm : MaskOk m s)
    (h : ∀ r ∉ [Reg.x2, .x3], s'.gpr r = s.gpr r) : MaskOk m s' := by
  cases m with
  | none => trivial
  | some r => exact ⟨hm.1, by rw [h r fun h' => hm.1 (List.mem_cons_of_mem _ h')]; exact hm.2⟩

/-- Word `i` of the operand: `p & m`, `0` above `p`'s `n` words. -/
def opw (m : Option Reg) (s : State) (base : Addr) (mo n i : Nat) : Nat :=
  if i < n then mk m s (word s.mem base (mo + 8 * i)).toNat else 0

theorem opw_lt (m : Option Reg) (s : State) (base : Addr) (mo n i : Nat) : opw m s base mo n i < 2 ^ 64 := by
  unfold opw; split
  · exact Nat.lt_of_le_of_lt (mk_le _ _ _) (BitVec.isLt _)
  · decide

/-- `x2 &= m`. -/
theorem and2_ok (s : State) (m : Reg) :
    WP isa (.block [.logic .and .x .x2 .x2 m]) s fun t =>
      t.gpr .x2 = s.gpr .x2 &&& s.gpr m ∧ Keeps [.x2] s t ∧ t.c = s.c := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

/-- `x2 = 0` (from `x12`). -/
theorem zero2_ok (s : State) (h12 : s.gpr .x12 = 0) :
    WP isa (.block [.add .x .x2 .x12 .x12]) s fun t => t.gpr .x2 = 0 ∧ Keeps [.x2] s t ∧ t.c = s.c := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left', h12]
  refine ⟨rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

/-- The operand's word `i` into `x2`. -/
theorem opnd_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {m : Option Reg}
    (hm : MaskOk m s) (h12 : s.gpr .x12 = 0) {mo n i : Nat} (hmo : mo + 8 * n ≤ size) (hmo8 : mo % 8 = 0) :
    WP isa (.block (opnd m mo n i)) s fun t =>
      (t.gpr .x2).toNat = opw m s base mo n i ∧ Keeps [.x2] s t ∧ t.c = s.c := by
  unfold opnd opw
  split
  · rename_i hi
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (ld_ok hs (d := mo + 8 * i) (by omega_arith) (by omega_arith) .x2) fun s₁ ⟨l₁, k₁, c₁⟩ => ?_
    cases m with
    | none => exact WP.block_nil ⟨by rw [l₁]; rfl, k₁, c₁⟩
    | some r =>
      refine WP.mono (and2_ok s₁ r) fun t ⟨a, k, c⟩ => ⟨?_, k₁.trans k, c.trans c₁⟩
      have hr : s₁.gpr r = s.gpr r := k₁.gpr _ fun h => hm.1 (by simp_all)
      rw [a, hr, and_mask hm.2, l₁]; rfl
  · exact WP.mono (zero2_ok s h12) fun t ⟨z, k, c⟩ => ⟨by rw [z]; rfl, k, c⟩

/-- An operand word added, or subtracted (as its complement). -/
def yw (sub : Bool) (x : Nat) : Nat := if sub then 2 ^ 64 - 1 - x else x

/-- `x3 = x3 ± x2` with carry `c` in. -/
theorem acc_ok (s : State) (sub : Bool) (first : Bool) {c : Bool} (hc : (if first then sub else s.c) = c) :
    WP isa (.block [if sub then (if first then .subs .x .x3 .x3 .x2 else .sbcs .x .x3 .x3 .x2)
      else (if first then .adds .x .x3 .x3 .x2 else .adcs .x .x3 .x3 .x2)]) s fun t =>
      (t.gpr .x3).toNat + 2 ^ 64 * t.c.toNat = (s.gpr .x3).toNat + yw sub (s.gpr .x2).toNat + c.toNat ∧
      Keeps [.x3] s t := by
  cases sub
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.mono (addc_ok s .x3 .x3 .x2 first (c := c) (by simpa using hc)) fun t ⟨d, c', k⟩ => ⟨?_, k⟩
    rw [d, c', Word64.addCarry_value]; rfl
  · simp only [↓reduceIte]
    refine WP.mono (subc_ok s .x3 .x3 .x2 first (c := c) (by simpa using hc)) fun t ⟨d, c', k⟩ => ⟨?_, k⟩
    rw [d, c', Word64.addCarry_value, BitVec.toNat_not]; rfl

/-- Word `i` of a chain. -/
theorem chainStep_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (sub : Bool)
    {m : Option Reg} (hm : MaskOk m s) (h12 : s.gpr .x12 = 0) {d mo n i : Nat}
    (hmo : mo + 8 * n ≤ size) (hmo8 : mo % 8 = 0) (hd : d + 8 * i + 8 ≤ size) (hd8 : d % 8 = 0) {c : Bool}
    (hc : (if i = 0 then sub else s.c) = c) :
    WP isa (.block (chainStep sub m d mo n i)) s fun t =>
      (word t.mem base (d + 8 * i)).toNat + 2 ^ 64 * t.c.toNat =
        (word s.mem base (d + 8 * i)).toNat + yw sub (opw m s base mo n i) + c.toNat ∧
      KeepRegs [.x2, .x3] s t ∧ Outside base (d + 8 * i) 8 s.mem t.mem := by
  have hn := hs.nowrap
  rw [chainStep, List.append_assoc, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ld_ok hs (d := d + 8 * i) hd (by omega_arith) .x3) fun s₁ ⟨l₁, k₁, c₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have g₁ : ∀ r ∉ [Reg.x2, .x3], s₁.gpr r = s.gpr r := fun r hr => k₁.gpr r (by simp_all)
  rw [WP.block_append_iff]
  refine WP.mono (opnd_ok hs₁ (maskOk_keep hm g₁) (by rw [g₁ _ (by decide), h12]) (i := i) hmo hmo8)
    fun s₂ ⟨o₂, k₂, c₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  have hc₂ : (if decide (i = 0) then sub else s₂.c) = c := by
    rw [c₂, c₁]; by_cases hi : i = 0 <;> simp_all
  have e : (if sub then (if i = 0 then Instr.subs .x .x3 .x3 .x2 else .sbcs .x .x3 .x3 .x2)
      else (if i = 0 then .adds .x .x3 .x3 .x2 else .adcs .x .x3 .x3 .x2)) =
      (if sub then (if decide (i = 0) then Instr.subs .x .x3 .x3 .x2 else .sbcs .x .x3 .x3 .x2)
      else (if decide (i = 0) then .adds .x .x3 .x3 .x2 else .adcs .x .x3 .x3 .x2)) := by
    by_cases hi : i = 0 <;> simp [hi]
  rw [e]
  refine WP.mono (acc_ok s₂ sub (decide (i = 0)) hc₂) fun s₃ ⟨a₃, k₃⟩ => ?_
  refine WP.mono (st_ok (hs₂.of_keeps k₃ (by decide)) (d := d + 8 * i) hd (by omega_arith) .x3) fun t et => ?_
  have mt : t.mem = s₃.mem.writeW (off base (d + 8 * i)) (s₃.gpr .x3) := by rw [et]
  have gt : t.gpr = s₃.gpr := by rw [et]
  have ct : t.c = s₃.c := by rw [et]
  have hm₃ : s₃.mem = s.mem := by rw [k₃.mem, k₂.mem, k₁.mem]
  have hopw : opw m s₁ base mo n i = opw m s base mo n i := by
    simp only [opw, mk_keep hm g₁, k₁.mem]
  refine ⟨?_, ⟨fun r hr => ?_, by rw [et]; exact k₃.rd.trans (k₂.rd.trans k₁.rd),
    by rw [et]; exact k₃.wr.trans (k₂.wr.trans k₁.wr), by rw [et]; exact k₃.sp.trans (k₂.sp.trans k₁.sp)⟩, ?_⟩
  · rw [mt, word_writeW_self, ct, a₃, o₂, hopw, k₂.gpr .x3 (by decide), l₁]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gt, k₃.gpr r (by simp [hr.2]), k₂.gpr r (by simp [hr.1]), k₁.gpr r (by simp [hr.2])]
  · rw [mt, hm₃]; exact writeW_outside _ _ _ (by omega_arith)

/-- Words `0 … j - 1` of a number given by its words. -/
def sumW (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => sumW f j + 2 ^ (64 * j) * f j

theorem sumW_compl (f : Nat → Nat) (hf : ∀ i, f i < 2 ^ 64) :
    ∀ j, sumW (fun i => 2 ^ 64 - 1 - f i) j + sumW f j + 1 = 2 ^ (64 * j)
  | 0 => rfl
  | j + 1 => by
    have ih := sumW_compl f hf j
    have := hf j
    simp only [sumW]
    rw [pow64_succ]
    have e : 2 ^ (64 * j) * (2 ^ 64 - 1 - f j) + 2 ^ (64 * j) * f j + 2 ^ (64 * j) = 2 ^ 64 * 2 ^ (64 * j) := by
      rw [← Nat.mul_add, ← Nat.mul_succ, Nat.mul_comm]; congr 1; omega_arith
    omega_arith

theorem sumW_opw (m : Option Reg) (s : State) (base : Addr) (mo n : Nat) :
    ∀ j, j ≤ n → sumW (opw m s base mo n) j = mk m s (wordsVal s.mem base mo j)
  | 0, _ => by cases m <;> simp [sumW, mk, wordsVal, masked]
  | j + 1, hj => by
    rw [sumW, sumW_opw m s base mo n j (by omega_arith), wordsVal_succ_top, mk_add, opw]
    simp only [show j < n by omega_arith, ↓reduceIte]

/-- Words `0 … j - 1` of a chain. -/
theorem chainRows_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (sub : Bool)
    {m : Option Reg} (hm : MaskOk m s) (h12 : s.gpr .x12 = 0) {d mo n : Nat}
    (hmo : mo + 8 * n ≤ size) (hmo8 : mo % 8 = 0) (hd : d + 8 * (n + 1) ≤ size) (hd8 : d % 8 = 0)
    (hsep : d + 8 * (n + 1) ≤ mo ∨ mo + 8 * n ≤ d) :
    ∀ j, j ≤ n + 1 → WP isa (.block ((List.range j).flatMap (chainStep sub m d mo n))) s fun t =>
      wordsVal t.mem base d j + 2 ^ (64 * j) * (if j = 0 then sub else t.c).toNat =
        wordsVal s.mem base d j + sumW (fun i => yw sub (opw m s base mo n i)) j + sub.toNat ∧
      KeepRegs [.x2, .x3] s t ∧ Outside base d (8 * j) s.mem t.mem
  | 0, _ => WP.block_nil ⟨by simp [wordsVal, sumW], ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | j + 1, hj => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (chainRows_ok hs sub hm h12 hmo hmo8 hd hd8 hsep j (by omega_arith)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have g₁ : ∀ r ∉ [Reg.x2, .x3], s₁.gpr r = s.gpr r := k₁.gpr
    refine WP.mono (chainStep_ok hs₁ sub (maskOk_keep hm g₁) (by rw [g₁ _ (by decide), h12]) (i := j) hmo hmo8
      (by omega_arith) hd8 (c := if j = 0 then sub else s₁.c) rfl) fun t ⟨e₂, k₂, O₂⟩ => ?_
    refine ⟨?_, k₁.trans k₂, fun x hx => by rw [O₂ x (by omega_arith), O₁ x (by omega_arith)]⟩
    have hopw : opw m s₁ base mo n j = opw m s base mo n j := by
      unfold opw; split
      · rw [mk_keep hm g₁, O₁.word (by omega_arith) (by omega_arith)]
      · rfl
    have hdj : word s₁.mem base (d + 8 * j) = word s.mem base (d + 8 * j) := O₁.word (by omega_arith) (by omega_arith)
    rw [hopw, hdj] at e₂
    rw [wordsVal_succ_top, O₂.wordsVal (by omega_arith) (by omega_arith), wordsVal_succ_top s.mem, sumW, pow64_succ]
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    generalize 2 ^ (64 * j) = A at *
    generalize (word t.mem base (d + 8 * j)).toNat = v at *
    generalize (word s.mem base (d + 8 * j)).toNat = w at *
    generalize yw sub (opw m s base mo n j) = y at *
    generalize (if j = 0 then sub else s₁.c) = c at *
    have h2 : A * (v + 2 ^ 64 * t.c.toNat) = A * (w + y + c.toNat) := by rw [e₂]
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_left_comm A (2 ^ 64)] at h2
    rw [Nat.mul_assoc (2 ^ 64) A]
    omega_arith

/-- `[d] = [d] + (p & m) mod 2^(64 (n + 1))`. -/
theorem chainAdd_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {m : Option Reg} (hm : MaskOk m s) (h12 : s.gpr .x12 = 0) {d mo n : Nat}
    (hmo : mo + 8 * n ≤ size) (hmo8 : mo % 8 = 0) (hd : d + 8 * (n + 1) ≤ size) (hd8 : d % 8 = 0)
    (hsep : d + 8 * (n + 1) ≤ mo ∨ mo + 8 * n ≤ d) :
    WP isa (.block (chain false m d mo n)) s fun t =>
      wordsVal t.mem base d (n + 1) =
        (wordsVal s.mem base d (n + 1) + mk m s (wordsVal s.mem base mo n)) % 2 ^ (64 * (n + 1)) ∧
      KeepRegs [.x2, .x3] s t ∧ Outside base d (8 * (n + 1)) s.mem t.mem := by
  refine WP.mono (chainRows_ok hs false hm h12 hmo hmo8 hd hd8 hsep (n + 1) (Nat.le_refl _))
    fun t ⟨e, k, O⟩ => ⟨?_, k, O⟩
  have hs : sumW (fun i => yw false (opw m s base mo n i)) (n + 1) = mk m s (wordsVal s.mem base mo n) := by
    simp only [yw, Bool.false_eq_true, ↓reduceIte]
    rw [sumW, sumW_opw m s base mo n n (Nat.le_refl _), opw]
    simp only [Nat.lt_irrefl, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
  simp only [hs, Nat.add_one_ne_zero, ↓reduceIte, Bool.toNat_false, Nat.add_zero] at e
  rw [← e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wordsVal_lt _ _ _ _)]

/-- `[d] = [d] - p mod 2^(64 (n + 1))`. -/
theorem chainSub_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (h12 : s.gpr .x12 = 0) {d mo n : Nat}
    (hmo : mo + 8 * n ≤ size) (hmo8 : mo % 8 = 0) (hd : d + 8 * (n + 1) ≤ size) (hd8 : d % 8 = 0)
    (hsep : d + 8 * (n + 1) ≤ mo ∨ mo + 8 * n ≤ d) :
    WP isa (.block (chain true none d mo n)) s fun t =>
      (wordsVal t.mem base d (n + 1) + wordsVal s.mem base mo n) % 2 ^ (64 * (n + 1)) =
        wordsVal s.mem base d (n + 1) ∧
      KeepRegs [.x2, .x3] s t ∧ Outside base d (8 * (n + 1)) s.mem t.mem := by
  refine WP.mono (chainRows_ok hs true (m := none) trivial h12 hmo hmo8 hd hd8 hsep (n + 1) (Nat.le_refl _))
    fun t ⟨e, k, O⟩ => ⟨?_, k, O⟩
  have hc := sumW_compl (opw none s base mo n) (opw_lt none s base mo n) (n + 1)
  have hP : sumW (opw none s base mo n) (n + 1) = wordsVal s.mem base mo n := by
    rw [sumW, sumW_opw none s base mo n n (Nat.le_refl _), opw]
    simp only [Nat.lt_irrefl, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
    rfl
  simp only [yw, ↓reduceIte] at e
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Bool.toNat_true] at e
  rw [hP] at hc
  have hlt := wordsVal_lt s.mem base d (n + 1)
  generalize 2 ^ (64 * (n + 1)) = M at *
  generalize sumW (fun i => 2 ^ 64 - 1 - opw none s base mo n i) (n + 1) = S at *
  -- `[d]' + M c = [d] + M - P`.
  have : wordsVal t.mem base d (n + 1) + wordsVal s.mem base mo n = wordsVal s.mem base d (n + 1) +
      M * (1 - t.c.toNat) := by
    have := Bool.toNat_le t.c
    rcases Nat.lt_or_ge t.c.toNat 1 with h | h
    · rw [show t.c.toNat = 0 by omega_arith] at e ⊢; omega_arith
    · rw [show t.c.toNat = 1 by omega_arith] at e ⊢; omega_arith
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-! ## The reduction -/

/-- `d = a b mod 2^64`. -/
theorem mulx_ok (s : State) (d a b : Reg) :
    WP isa (.block [.mul .x d a b]) s fun t =>
      (t.gpr d).toNat = (s.gpr a).toNat * (s.gpr b).toNat % 2 ^ 64 ∧ Keeps [d] s t ∧ t.c = s.c := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨mul_toNat _ _, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

theorem KeepRegs.of_st {rs : List Reg} {s u : State} {m' : Mem} (h : u = { s with mem := m' }) :
    KeepRegs rs s u := by
  subst h; exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

/-- The start of the reduction: `x16 = t₀ m mod 2^64`, and `[t]` sign-extended. -/
theorem mredHead_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (h12 : s.gpr .x12 = 0)
    {M : Mod} {t : Nat} (ht : t + 8 * (M.n + 2) ≤ size) (ht8 : t % 8 = 0) :
    WP isa (.block (mredHead M t)) s fun u =>
      (u.gpr .x16).toNat = (word s.mem base t).toNat * M.minv.toNat % 2 ^ 64 ∧
      wordsVal u.mem base t (M.n + 2) =
        wordsVal s.mem base t (M.n + 1) + 2 ^ (64 * (M.n + 1)) * sgnW (word s.mem base (t + 8 * M.n)) ∧
      KeepRegs [.x2, .x3, .x9, .x16, .x17] s u ∧ Outside base (t + 8 * (M.n + 1)) 8 s.mem u.mem := by
  have hn := hs.nowrap
  simp only [mredHead, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs (d := t) (by omega_arith) ht8 .x2) fun s₁ ⟨l₁, k₁, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s₁ .x17 M.minv) fun s₂ ⟨c₂, k₂⟩ => ?_
  rw [WP.block_append_iff, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (mulx_ok s₂ .x16 .x2 .x17) fun s₃ ⟨m₃, k₃, _⟩ => ?_
  have hs₃ : Scr s₃ base size := ((hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  refine WP.mono (ld_ok hs₃ (d := t + 8 * M.n) (by omega_arith) (by omega_arith) .x3) fun s₄ ⟨l₄, k₄, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sgnMask_ok s₄ (by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide),
    k₁.gpr _ (by decide), h12])) fun s₅ ⟨g₅, _, k₅, _⟩ => ?_
  refine WP.mono (st_ok ((hs₃.of_keeps k₄ (by decide)).of_keeps k₅ (by decide)) (d := t + 8 * (M.n + 1))
    (by omega_arith) (by omega_arith) .x9) fun u eu => ?_
  have mu : u.mem = s₅.mem.writeW (off base (t + 8 * (M.n + 1))) (s₅.gpr .x9) := by rw [eu]
  have gu : u.gpr = s₅.gpr := by rw [eu]
  have hm₅ : s₅.mem = s.mem := by rw [k₅.mem, k₄.mem, k₃.mem, k₂.mem, k₁.mem]
  have Oj := writeW_outside s₅.mem base (d := t + 8 * (M.n + 1)) (s₅.gpr .x9) (by omega_arith)
  refine ⟨?_, ?_, ((((((Keeps.regs k₁).mono (by decide)).trans ((Keeps.regs k₂).mono (by decide))).trans
    ((Keeps.regs k₃).mono (by decide))).trans ((Keeps.regs k₄).mono (by decide))).trans ((Keeps.regs k₅).mono (by decide))).trans
    (KeepRegs.of_st eu), fun x hx => by rw [mu, Oj x hx, hm₅]⟩
  · rw [gu, k₅.gpr _ (by decide), k₄.gpr _ (by decide), m₃, k₂.gpr _ (by decide), c₂, l₁]
  · rw [show M.n + 2 = M.n + 1 + 1 from rfl, mu, wordsVal_succ_top, word_writeW_self,
      Oj.wordsVal (by omega_arith) (by omega_arith), hm₅, g₅, l₄, k₃.mem, k₂.mem, k₁.mem]

/-- `[dst] = mred p m T` (`n` words), for `[t]` (`n + 1` words) holding `T`, `|T| ≤ 2^63 p`. -/
theorem mredC_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {p : Nat}
    (hM : ModOkA M size p s.mem base) (hmo8 : M.mo % 8 = 0) (h12 : s.gpr .x12 = 0) {dst t : Nat}
    (ht : t + 8 * (M.n + 2) ≤ size) (ht8 : t % 8 = 0) (hd : dst + 8 * M.n ≤ size) (hd8 : dst % 8 = 0)
    (htm : t + 8 * (M.n + 2) ≤ M.mo ∨ M.mo + 8 * M.n ≤ t) (hdt : dst + 8 * M.n ≤ t ∨ t + 8 * (M.n + 2) ≤ dst)
    {T : Int} (hT : |T| ≤ 2 ^ 63 * p)
    (hW : (wordsVal s.mem base t (M.n + 1) : Int) % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) =
      T % ((2 ^ (64 * (M.n + 1)) : Nat) : Int)) :
    WP isa (.block (mredC M dst t)) s fun u =>
      (wordsVal u.mem base dst M.n : Int) = Divstep.mred p M.minv.toNat T ∧
      KeepRegs [.x2, .x3, .x8, .x9, .x10, .x16, .x17] s u ∧
      ∃ m₁, Outside base t (8 * (M.n + 2)) s.mem m₁ ∧ Outside base dst (8 * M.n) m₁ u.mem := by
  have hn := hs.nowrap
  have hP : wordsVal s.mem base M.mo M.n = p := hM.val
  have hmo := hM.mo
  simp only [mredC, List.append_assoc]
  -- `x16 = k`, `[t]` sign-extended.
  rw [WP.block_append_iff]
  refine WP.mono (mredHead_ok hs h12 ht ht8) fun s₁ ⟨x₁, e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have z₁ : s₁.gpr .x12 = 0 := by rw [k₁.gpr _ (by decide), h12]
  have P₁ : wordsVal s₁.mem base M.mo M.n = p := by rw [O₁.wordsVal (by omega_arith) (by omega_arith), hP]
  -- `[t] += k p`.
  rw [WP.block_append_iff]
  refine WP.mono (mulAdd_ok hs₁ (w := .x16) (by decide) z₁ (dst := t) (src := M.mo) (k := M.n) (K := M.n + 2)
    (by omega_arith) hmo hmo8 ht ht8 htm) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have z₂ : s₂.gpr .x12 = 0 := by rw [k₂.gpr _ (by decide), z₁]
  have P₂ : wordsVal s₂.mem base M.mo M.n = p := by rw [O₂.wordsVal (by omega_arith) (by omega_arith), P₁]
  -- `r`'s sign.
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs₂ (d := t + 8 * (M.n + 1)) (by omega_arith) (by omega_arith) .x3) fun s₃ ⟨l₃, k₃, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sgnMask_ok s₃ (by rw [k₃.gpr _ (by decide), z₂])) fun s₄ ⟨g₄, mk₄, k₄, _⟩ => ?_
  have hs₄ := (hs₂.of_keeps k₃ (by decide)).of_keeps k₄ (by decide)
  have z₄ : s₄.gpr .x12 = 0 := by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), z₂]
  have m₄ : s₄.mem = s₂.mem := by rw [k₄.mem, k₃.mem]
  -- `R₁ = R + (p if negative)`.
  rw [WP.block_append_iff]
  refine WP.mono (chainAdd_ok hs₄ (m := some .x9) ⟨by decide, mk₄⟩ z₄ (d := t + 8) (mo := M.mo) (n := M.n) hmo
    hmo8 (by omega_arith) (by omega_arith) (by omega_arith)) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  have z₅ : s₅.gpr .x12 = 0 := by rw [k₅.gpr _ (by decide), z₄]
  have P₅ : wordsVal s₅.mem base M.mo M.n = p := by rw [O₅.wordsVal (by omega_arith) (by omega_arith), m₄, P₂]
  -- `R₂ = R₁ - p`.
  rw [WP.block_append_iff]
  refine WP.mono (chainSub_ok hs₅ z₅ (d := t + 8) (mo := M.mo) (n := M.n) hmo hmo8 (by omega_arith) (by omega_arith)
    (by omega_arith)) fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  have z₆ : s₆.gpr .x12 = 0 := by rw [k₆.gpr _ (by decide), z₅]
  have P₆ : wordsVal s₆.mem base M.mo M.n = p := by rw [O₆.wordsVal (by omega_arith) (by omega_arith), P₅]
  -- `R₂`'s sign.
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs₆ (d := t + 8 * (M.n + 1)) (by omega_arith) (by omega_arith) .x3) fun s₇ ⟨l₇, k₇, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sgnMask_ok s₇ (by rw [k₇.gpr _ (by decide), z₆])) fun s₈ ⟨g₈, mk₈, k₈, _⟩ => ?_
  have hs₈ := (hs₆.of_keeps k₇ (by decide)).of_keeps k₈ (by decide)
  have z₈ : s₈.gpr .x12 = 0 := by rw [k₈.gpr _ (by decide), k₇.gpr _ (by decide), z₆]
  have m₈ : s₈.mem = s₆.mem := by rw [k₈.mem, k₇.mem]
  -- `R₃ = R₂ + (p if negative)`.
  rw [WP.block_append_iff]
  refine WP.mono (chainAdd_ok hs₈ (m := some .x9) ⟨by decide, mk₈⟩ z₈ (d := t + 8) (mo := M.mo) (n := M.n) hmo
    hmo8 (by omega_arith) (by omega_arith) (by omega_arith)) fun s₉ ⟨e₉, k₉, O₉⟩ => ?_
  have hs₉ := hs₈.of_keepRegs k₉ (by decide)
  -- `[dst] = R₃`.
  refine WP.mono (copyW_ok hs₉ (dst := dst) (src := t + 8) (by omega_arith) hd8 M.n (by omega_arith) hd (by omega_arith))
    fun u ⟨eu, ku, Ou⟩ => ?_
  refine ⟨?_, ((((((((((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans
    ((Keeps.regs k₃).mono (by decide))).trans ((Keeps.regs k₄).mono (by decide))).trans (k₅.mono (by decide))).trans
    (k₆.mono (by decide))).trans ((Keeps.regs k₇).mono (by decide))).trans ((Keeps.regs k₈).mono (by decide))).trans
    (k₉.mono (by decide))).trans (ku.mono (by decide))), s₉.mem, ?_, Ou⟩
  rotate_left
  · intro x hx
    rw [O₉ x (by omega_arith), m₈, O₆ x (by omega_arith), O₅ x (by omega_arith), m₄, O₂ x hx, O₁ x (by omega_arith)]
  -- The arithmetic.
  have hp0 : 0 < p := by
    have := hM.inv
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [h, Nat.zero_mul] at this; exact absurd this (by decide)
    · exact h
  have hpA : p < 2 ^ (64 * M.n) := hP ▸ wordsVal_lt _ _ _ _
  have hQ : 2 ^ (64 * (M.n + 1)) = 2 ^ (64 * M.n) * 2 ^ 64 := by rw [pow64_succ, Nat.mul_comm]
  have hQ' : 2 ^ (64 * (M.n + 2)) = 2 ^ (64 * M.n) * 2 ^ 64 * 2 ^ 64 := by
    rw [show M.n + 2 = M.n + 1 + 1 from rfl, pow64_succ, hQ, Nat.mul_comm]
  have eR : wordsVal s₂.mem base t (M.n + 2) % 2 ^ 64 + 2 ^ 64 * wordsVal s₂.mem base (t + 8) (M.n + 1) =
      wordsVal s₂.mem base t (M.n + 2) := by
    rw [show M.n + 2 = M.n + 1 + 1 from rfl, wordsVal, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (BitVec.isLt _)]
  have l₃' : s₃.gpr .x3 = word s₂.mem base (t + 8 + 8 * M.n) := by
    rw [l₃, show t + 8 * (M.n + 1) = t + 8 + 8 * M.n by omega_arith]
  have l₇' : s₇.gpr .x3 = word s₆.mem base (t + 8 + 8 * M.n) := by
    rw [l₇, show t + 8 * (M.n + 1) = t + 8 + 8 * M.n by omega_arith]
  have key := Divstep.mred_nat (A := 2 ^ (64 * M.n)) (B := 2 ^ 64) (H := 2 ^ 63) (p := p) (m := M.minv.toNat)
    (t := T) (W := wordsVal s.mem base t (M.n + 1)) (k := (s₁.gpr .x16).toNat)
    (E := wordsVal s₂.mem base t (M.n + 2)) (R := wordsVal s₂.mem base (t + 8) (M.n + 1))
    (R₁ := wordsVal s₅.mem base (t + 8) (M.n + 1)) (R₂ := wordsVal s₆.mem base (t + 8) (M.n + 1))
    (R₃ := wordsVal s₉.mem base (t + 8) (M.n + 1))
    rfl rfl (Nat.two_pow_pos _) hp0 hpA hM.inv hT (hQ ▸ wordsVal_lt _ _ _ _) (by rw [← hQ]; exact hW)
    (by rw [x₁, wordsVal, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (BitVec.isLt _)])
    (by rw [e₂, e₁, P₁, sgnW_top, hQ', hQ])
    (by have := eR; omega_arith)
    (by rw [e₅]; simp only [mk]; rw [masked_top (by rw [g₄, l₃']), m₄, P₂, hQ])
    (hQ ▸ wordsVal_lt _ _ _ _) (by rw [P₅, hQ] at e₆; exact e₆)
    (by rw [e₉]; simp only [mk]; rw [masked_top (by rw [g₈, l₇']), m₈, P₆, hQ])
  obtain ⟨r0, r1⟩ := Divstep.mred_range (p := p) (m := M.minv.toNat) (t := T) (by exact_mod_cast hp0)
    (by exact_mod_cast hM.inv) hT
  have hR₃ : wordsVal s₉.mem base (t + 8) (M.n + 1) < 2 ^ (64 * M.n) := by omega_arith
  have hlow : wordsVal s₉.mem base (t + 8) M.n = wordsVal s₉.mem base (t + 8) (M.n + 1) := by
    have h := congrArg (· % 2 ^ (64 * M.n)) (wordsVal_succ_top s₉.mem base (t + 8) M.n)
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wordsVal_lt _ _ _ _), Nat.mod_eq_of_lt hR₃] at h
    exact h.symm
  rw [eu, hlow, key]

end VG.Proof.Weierstrass.AArch64
