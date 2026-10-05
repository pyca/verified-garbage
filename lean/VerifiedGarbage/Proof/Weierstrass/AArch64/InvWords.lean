import VerifiedGarbage.Impl.Weierstrass.AArch64.Inv
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.Csub

/-!
# Inversion by divsteps on AArch64: numbers of several words

The memory operations of a batch, on words at offsets of `x0` in the
working space, as numbers: `w [src] mod 2^(64 K)` (`mulw_ok`), its
accumulation (`mulAdd_ok`), the masked shifted subtraction (`subSh_ok`), the
arithmetic shift by 59 (`shr59_ok`), and copies.
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

theorem umulh_le (a b : BitVec 64) : a.toNat * b.toNat / 2 ^ 64 ≤ 2 ^ 64 - 2 := by
  have ha := a.isLt; have hb := b.isLt
  have : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : (2 ^ 64 - 1) * (2 ^ 64 - 1) / 2 ^ 64 = 2 ^ 64 - 2 := by decide
  rw [← h2]; exact Nat.div_le_div_right this

theorem mul_toNat (a b : BitVec 64) : (a * b).toNat = a.toNat * b.toNat % 2 ^ 64 := BitVec.toNat_mul a b

/-- `x8 + 2^64 x10 = w x2` (the first word of a product row). -/
theorem ml0_ok (s : State) {w : Reg} (hw : w ∉ [Reg.x8, .x10]) :
    WP isa (.block [.mul .x .x8 w .x2, .umulh .x10 w .x2]) s fun t =>
      (t.gpr .x8).toNat + 2 ^ 64 * (t.gpr .x10).toNat = (s.gpr w).toNat * (s.gpr .x2).toNat ∧
      Keeps [.x8, .x10] s t ∧ t.c = s.c := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write, BitVec.setWidth_eq,
    reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left', hw.1]
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  · rw [mul_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (umulh_le _ _) (by decide))]
    exact Nat.mod_add_div _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ↓reduceIte]

/-- `x8 + 2^64 h' = w x2 + x10`, `h'` into `hd` (`x9` or `x10`): a word of a product row. -/
theorem mla4_ok (s : State) {w hd : Reg} (hw : w ∉ [Reg.x8, .x9, .x10]) (hd' : hd = .x9 ∨ hd = .x10)
    (h12 : s.gpr .x12 = 0) :
    WP isa (.block [.mul .x .x8 w .x2, .umulh .x9 w .x2, .adds .x .x8 .x8 .x10, .adc .x hd .x9 .x12]) s fun t =>
      (t.gpr .x8).toNat + 2 ^ 64 * (t.gpr hd).toNat = (s.gpr w).toNat * (s.gpr .x2).toNat + (s.gpr .x10).toNat ∧
      Keeps [.x8, .x9, .x10] s t := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw
  obtain ⟨hw8, hw9, hw10⟩ := hw
  have hP := umulh_le (s.gpr w) (s.gpr .x2)
  apply WP.of_runBlock
  rcases hd' with rfl | rfl <;>
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write, BitVec.setWidth_eq,
      RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, reduceCtorEq, ↓reduceIte,
      Option.some.injEq, exists_eq_left', hw8, h12]
    refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    · simp only [BitVec.toNat_add, BitVec.toNat_ofNat, mul_toNat, Bool.toNat, BitVec.ofNat_eq_ofNat,
        Bool.cond_decide, Bool.cond_false, Nat.zero_mod, Nat.add_zero, BitVec.toNat_ofNat, Nat.mod_mod]
      have := Nat.mod_add_div ((s.gpr w).toNat * (s.gpr .x2).toNat) (2 ^ 64)
      have hx10 := (s.gpr .x10).isLt
      dsimp only [Size.bits]
      generalize (s.gpr w).toNat * (s.gpr .x2).toNat = P at this hP ⊢
      generalize (s.gpr .x10).toNat = h at hx10 ⊢
      split <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2, ↓reduceIte]

/-- Word `j` of `[src]`, through stores outside `[src]`. -/
theorem word_out {m m' : Mem} {base : Addr} {o n d : Nat} (h : Outside base o n m m') (hd : d + 8 ≤ o ∨ o + n ≤ d)
    (hd' : d + 8 ≤ 2 ^ 64) : word m' base d = word m base d := h.word hd hd'

/-- A row's words so far, and the next. -/
theorem row_arith {Wd A x8 x10' x10 wv xv Ws : Nat} (e₁ : Wd + A * x10 = wv * Ws)
    (e₃ : x8 + 2 ^ 64 * x10' = wv * xv + x10) : Wd + A * x8 + 2 ^ 64 * A * x10' = wv * (Ws + A * xv) := by
  have h : A * (x8 + 2 ^ 64 * x10') = A * (wv * xv + x10) := by rw [e₃]
  rw [Nat.mul_add, Nat.mul_add] at h
  rw [Nat.mul_add, Nat.mul_left_comm wv A xv, Nat.mul_comm (2 ^ 64) A, Nat.mul_assoc A (2 ^ 64)]
  omega

/-- The words `0 … j` of `w [src]` (`1 ≤ j`): `[dst] + 2^(64 j) x10 = w [src]`. -/
theorem mulwRows_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {w : Reg}
    (hw : w ∉ [Reg.x0, .x2, .x8, .x9, .x10]) (h12 : s.gpr .x12 = 0) {dst src k : Nat}
    (hsrc : src + 8 * k ≤ size) (hs8 : src % 8 = 0) (hdst : dst + 8 * k ≤ size) (hd8 : dst % 8 = 0)
    (hsep : dst + 8 * k ≤ src ∨ src + 8 * k ≤ dst) :
    ∀ j, 1 ≤ j → j ≤ k → WP isa (.block ((List.range j).flatMap (mulwStep w dst src))) s fun t =>
      wordsVal t.mem base dst j + 2 ^ (64 * j) * (t.gpr .x10).toNat = (s.gpr w).toNat * wordsVal s.mem base src j ∧
      KeepRegs [.x2, .x8, .x9, .x10] s t ∧ Outside base dst (8 * j) s.mem t.mem
  | 0, h, _ => absurd h (by decide)
  | j + 1, _, hj => by
    have hn := hs.nowrap
    have hw' := hw
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw
    obtain ⟨hw0, hw2, hw8, hw9, hw10⟩ := hw
    rcases Nat.lt_or_ge j 1 with h0 | h1
    · -- The first word.
      obtain rfl : j = 0 := by omega
      simp only [List.range_one, List.flatMap_singleton, mulwStep, ↓reduceIte, Nat.zero_add]
      rw [← List.singleton_append, WP.block_append_iff]
      refine WP.mono (ld_ok hs (d := src) (by omega) hs8 .x2) fun s₁ ⟨l₁, k₁, _⟩ => ?_
      rw [show ([.mul .x .x8 w .x2, .umulh .x10 w .x2, st .x8 dst] : List Instr) =
        [.mul .x .x8 w .x2, .umulh .x10 w .x2] ++ [st .x8 dst] from rfl, WP.block_append_iff]
      refine WP.mono (ml0_ok s₁ (w := w) (by simp [hw8, hw10])) fun s₂ ⟨e₂, k₂, _⟩ => ?_
      have hs₂ : Scr s₂ base size := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
      refine WP.mono (st_ok hs₂ (d := dst) (by omega) hd8 .x8) fun t et => ?_
      have mt : t.mem = s₂.mem.writeW (off base dst) (s₂.gpr .x8) := by rw [et]
      have gt : t.gpr = s₂.gpr := by rw [et]
      have hw₁ : s₁.gpr w = s.gpr w := k₁.gpr _ (by simp [hw2])
      refine ⟨?_, ⟨fun r hr => ?_, by rw [et]; exact k₂.rd.trans k₁.rd, by rw [et]; exact k₂.wr.trans k₁.wr,
        by rw [et]; exact k₂.sp.trans k₁.sp⟩, ?_⟩
      · simp only [wordsVal, Nat.mul_one, Nat.mul_zero, Nat.add_zero]
        rw [mt, word_writeW_self, gt, e₂, hw₁, l₁]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [gt, k₂.gpr r (by simp [hr.2.1, hr.2.2.2]), k₁.gpr r (by simp [hr.1])]
      · rw [mt, k₂.mem, k₁.mem]; exact writeW_outside _ _ _ (by omega)
    · -- Word `j ≥ 1`.
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
      refine WP.mono (mulwRows_ok hs hw' h12 hsrc hs8 hdst hd8 hsep j h1 (by omega))
        fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
      have hs₁ := hs.of_keepRegs k₁ (by decide)
      simp only [mulwStep, show ¬ j = 0 by omega, ↓reduceIte]
      rw [← List.singleton_append, WP.block_append_iff]
      refine WP.mono (ld_ok hs₁ (d := src + 8 * j) (by omega) (by omega) .x2) fun s₂ ⟨l₂, k₂, _⟩ => ?_
      rw [show ([.mul .x .x8 w .x2, .umulh .x9 w .x2, .adds .x .x8 .x8 .x10, .adc .x .x10 .x9 .x12,
          st .x8 (dst + 8 * j)] : List Instr) = [.mul .x .x8 w .x2, .umulh .x9 w .x2, .adds .x .x8 .x8 .x10,
          .adc .x .x10 .x9 .x12] ++ [st .x8 (dst + 8 * j)] from rfl, WP.block_append_iff]
      have h12₂ : s₂.gpr .x12 = 0 := by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), h12]
      refine WP.mono (mla4_ok s₂ (w := w) (hd := .x10) (by simp [hw8, hw9, hw10]) (Or.inr rfl) h12₂)
        fun s₃ ⟨e₃, k₃⟩ => ?_
      have hs₃ : Scr s₃ base size := (hs₁.of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
      refine WP.mono (st_ok hs₃ (d := dst + 8 * j) (by omega) (by omega) .x8) fun t et => ?_
      have mt : t.mem = s₃.mem.writeW (off base (dst + 8 * j)) (s₃.gpr .x8) := by rw [et]
      have gt : t.gpr = s₃.gpr := by rw [et]
      have hw₂ : s₂.gpr w = s.gpr w := by
        rw [k₂.gpr _ (by simp [hw2]), k₁.gpr _ (by simp [hw2, hw8, hw9, hw10])]
      have hx10 : s₂.gpr .x10 = s₁.gpr .x10 := k₂.gpr _ (by decide)
      have hm₃ : s₃.mem = s₁.mem := by rw [k₃.mem, k₂.mem]
      have hsrcj : word s₁.mem base (src + 8 * j) = word s.mem base (src + 8 * j) :=
        word_out O₁ (by omega) (by omega)
      have Oj := writeW_outside s₃.mem base (d := dst + 8 * j) (s₃.gpr .x8) (by omega)
      refine ⟨?_, ⟨fun r hr => ?_, by rw [et]; exact k₃.rd.trans (k₂.rd.trans k₁.rd),
        by rw [et]; exact k₃.wr.trans (k₂.wr.trans k₁.wr), by rw [et]; exact k₃.sp.trans (k₂.sp.trans k₁.sp)⟩, ?_⟩
      · rw [mt, wordsVal_succ_top, word_writeW_self, Oj.wordsVal (by omega) (by omega), hm₃,
          wordsVal_succ_top s.mem base src j, ← hsrcj, ← l₂, gt, pow64_succ]
        rw [hw₂, hx10] at e₃
        exact row_arith e₁ e₃
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [gt, k₃.gpr r (by simp [hr.2.1, hr.2.2.1, hr.2.2.2]), k₂.gpr r (by simp [hr.1]),
          k₁.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])]
      · intro x hx
        rw [mt, Oj x (by omega), hm₃, O₁ x (by omega)]

/-- `[o] = 0` (`m` words, from `x12 = 0`). -/
theorem zerosW_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (h12 : s.gpr .x12 = 0)
    {o : Nat} (ho8 : o % 8 = 0) : ∀ m, o + 8 * m ≤ size →
    WP isa (.block (zerosW o m)) s fun t =>
      wordsVal t.mem base o m = 0 ∧ KeepRegs [] s t ∧ Outside base o (8 * m) s.mem t.mem
  | 0, _ => WP.block_nil ⟨rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | m + 1, hm => by
    have hn := hs.nowrap
    rw [zerosW, List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zerosW_ok hs h12 ho8 m (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    refine WP.mono (st_ok hs₁ (d := o + 8 * m) (by omega) (by omega) .x12) fun t et => ?_
    have mt : t.mem = s₁.mem.writeW (off base (o + 8 * m)) (s₁.gpr .x12) := by rw [et]
    have Oj := writeW_outside s₁.mem base (d := o + 8 * m) (s₁.gpr .x12) (by omega)
    refine ⟨?_, ⟨fun r _ => by rw [et]; exact k₁.gpr r List.not_mem_nil, by rw [et]; exact k₁.rd,
      by rw [et]; exact k₁.wr, by rw [et]; exact k₁.sp⟩, fun x hx => by rw [mt, Oj x (by omega), O₁ x (by omega)]⟩
    rw [mt, wordsVal_succ_top, word_writeW_self, Oj.wordsVal (by omega) (by omega), e₁,
      k₁.gpr _ List.not_mem_nil, h12]
    rfl

/-- Words `0 … a + b` of a number: the first `a`, then `b` more. -/
theorem wordsVal_split (m : Mem) (base : Addr) (d a : Nat) :
    ∀ b, wordsVal m base d (a + b) = wordsVal m base d a + 2 ^ (64 * a) * wordsVal m base (d + 8 * a) b
  | 0 => by simp [wordsVal]
  | b + 1 => by
    rw [← Nat.add_assoc, wordsVal_succ_top, wordsVal_split m base d a b, wordsVal_succ_top m base (d + 8 * a) b,
      show d + 8 * a + 8 * b = d + 8 * (a + b) by omega, show 64 * (a + b) = 64 * a + 64 * b by omega, Nat.pow_add,
      Nat.mul_add (2 ^ (64 * a)), ← Nat.mul_assoc (2 ^ (64 * a))]
    omega

/-- `w x < 2^(64 (k + 1))` for a word `w` and `x < 2^(64 k)`. -/
theorem word_mul_lt (w : BitVec 64) {x k : Nat} (hx : x < 2 ^ (64 * k)) : w.toNat * x < 2 ^ (64 * (k + 1)) := by
  rw [pow64_succ]
  calc w.toNat * x ≤ (2 ^ 64 - 1) * x := Nat.mul_le_mul_right _ (by have := w.isLt; omega)
    _ < 2 ^ 64 * 2 ^ (64 * k) := by
      have : (2 ^ 64 - 1) * x ≤ (2 ^ 64 - 1) * (2 ^ (64 * k) - 1) := Nat.mul_le_mul_left _ (by omega)
      have h2 : (2 ^ 64 - 1) * (2 ^ (64 * k) - 1) < 2 ^ 64 * 2 ^ (64 * k) := by
        have := Nat.two_pow_pos (64 * k)
        calc (2 ^ 64 - 1) * (2 ^ (64 * k) - 1) ≤ (2 ^ 64 - 1) * 2 ^ (64 * k) := Nat.mul_le_mul_left _ (by omega)
          _ < 2 ^ 64 * 2 ^ (64 * k) := Nat.mul_lt_mul_of_pos_right (by omega) this
      omega

/-- `[dst] = w [src] mod 2^(64 K)`. -/
theorem mulw_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {w : Reg}
    (hw : w ∉ [Reg.x0, .x2, .x8, .x9, .x10]) (h12 : s.gpr .x12 = 0) {dst src k K : Nat} (h1 : 1 ≤ k) (hkK : k ≤ K)
    (hsrc : src + 8 * k ≤ size) (hs8 : src % 8 = 0) (hdst : dst + 8 * K ≤ size) (hd8 : dst % 8 = 0)
    (hsep : dst + 8 * K ≤ src ∨ src + 8 * k ≤ dst) :
    WP isa (.block (mulw w dst src k K)) s fun t =>
      wordsVal t.mem base dst K = (s.gpr w).toNat * wordsVal s.mem base src k % 2 ^ (64 * K) ∧
      KeepRegs [.x2, .x8, .x9, .x10] s t ∧ Outside base dst (8 * K) s.mem t.mem := by
  have hn := hs.nowrap
  rw [mulw, WP.block_append_iff]
  refine WP.mono (mulwRows_ok hs hw h12 hsrc hs8 (by omega) hd8 (by omega) k h1 (Nat.le_refl _))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have hlt := wordsVal_lt s₁.mem base dst k
  have hwS := word_mul_lt (s.gpr w) (wordsVal_lt s.mem base src k)
  split
  · rename_i hk
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (st_ok hs₁ (d := dst + 8 * k) (by omega) (by omega) .x10) fun s₂ e₂ => ?_
    have m₂ : s₂.mem = s₁.mem.writeW (off base (dst + 8 * k)) (s₁.gpr .x10) := by rw [e₂]
    have hs₂ : Scr s₂ base size := by rw [e₂]; exact ⟨hs₁.x0, hs₁.wr, hs₁.nowrap, hs₁.enc⟩
    have h12₂ : s₂.gpr .x12 = 0 := by rw [e₂]; exact (k₁.gpr _ (by decide)).trans h12
    refine WP.mono (zerosW_ok hs₂ h12₂ (o := dst + 8 * (k + 1)) (by omega) (K - k - 1) (by omega))
      fun t ⟨e₃, k₃, O₃⟩ => ?_
    have Ok := writeW_outside s₁.mem base (d := dst + 8 * k) (s₁.gpr .x10) (by omega)
    have k₂ : KeepRegs [.x2, .x8, .x9, .x10] s₁ s₂ := by rw [e₂]; exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
    refine ⟨?_, (k₁.trans k₂).trans (k₃.mono (fun _ h => absurd h List.not_mem_nil)),
      fun x hx => by rw [O₃ x (by omega), m₂, Ok x (by omega), O₁ x (by omega)]⟩
    -- The words: `[dst]`'s first `k`, then `x10`, then zeros.
    rw [show K = (k + 1) + (K - k - 1) by omega, wordsVal_split, e₃, Nat.mul_zero, Nat.add_zero,
      wordsVal_succ_top, O₃.word (by omega) (by omega), O₃.wordsVal (by omega) (by omega), m₂, word_writeW_self,
      Ok.wordsVal (by omega) (by omega), Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hwS
        (Nat.pow_le_pow_right (by decide) (by omega))), e₁]
  · rename_i hk
    obtain rfl : K = k := by omega
    refine WP.block_nil ⟨?_, k₁, O₁⟩
    rw [← e₁, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- `x3 + 2^64 x10 = x3 + x8 + 2^64 x9`, if that is below `2^128`. -/
theorem add2_ok (s : State) (h12 : s.gpr .x12 = 0)
    (hb : (s.gpr .x3).toNat + (s.gpr .x8).toNat + 2 ^ 64 * (s.gpr .x9).toNat < 2 ^ 128) :
    WP isa (.block [.adds .x .x3 .x3 .x8, .adc .x .x10 .x9 .x12]) s fun t =>
      (t.gpr .x3).toNat + 2 ^ 64 * (t.gpr .x10).toNat =
        (s.gpr .x3).toNat + (s.gpr .x8).toNat + 2 ^ 64 * (s.gpr .x9).toNat ∧ Keeps [.x3, .x10] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write, BitVec.setWidth_eq,
    RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, reduceCtorEq, ↓reduceIte,
    Option.some.injEq, exists_eq_left', h12]
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Bool.toNat, BitVec.ofNat_eq_ofNat,
      Bool.cond_decide, Bool.cond_false, Nat.zero_mod, Nat.add_zero, Nat.mod_mod]
    dsimp only [Size.bits]
    have h3 := (s.gpr .x3).isLt; have h8 := (s.gpr .x8).isLt; have h9 := (s.gpr .x9).isLt
    generalize (s.gpr .x3).toNat = a at *
    generalize (s.gpr .x8).toNat = b at *
    generalize (s.gpr .x9).toNat = c at *
    split <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2, ↓reduceIte]

/-- Word `i` of `[dst] += w [src]`: `dst_i' + 2^64 h' = dst_i + w src_i + h`. -/
theorem mulAddStep_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {w : Reg}
    (hw : w ∉ [Reg.x0, .x2, .x3, .x8, .x9, .x10]) (h12 : s.gpr .x12 = 0) {si di : Nat}
    (hsi : si + 8 ≤ size) (hsi8 : si % 8 = 0) (hdi : di + 8 ≤ size) (hdi8 : di % 8 = 0) :
    WP isa (.block [ld .x2 si, .mul .x .x8 w .x2, .umulh .x9 w .x2, .adds .x .x8 .x8 .x10,
      .adc .x .x9 .x9 .x12, ld .x3 di, .adds .x .x3 .x3 .x8, .adc .x .x10 .x9 .x12, st .x3 di]) s fun t =>
      (word t.mem base di).toNat + 2 ^ 64 * (t.gpr .x10).toNat =
        (word s.mem base di).toNat + (s.gpr w).toNat * (word s.mem base si).toNat + (s.gpr .x10).toNat ∧
      KeepRegs [.x2, .x3, .x8, .x9, .x10] s t ∧ Outside base di 8 s.mem t.mem := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw
  obtain ⟨hw0, hw2, hw3, hw8, hw9, hw10⟩ := hw
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ld_ok hs hsi hsi8 .x2) fun s₁ ⟨l₁, k₁, _⟩ => ?_
  rw [show ([.mul .x .x8 w .x2, .umulh .x9 w .x2, .adds .x .x8 .x8 .x10, .adc .x .x9 .x9 .x12, ld .x3 di,
      .adds .x .x3 .x3 .x8, .adc .x .x10 .x9 .x12, st .x3 di] : List Instr) =
    [.mul .x .x8 w .x2, .umulh .x9 w .x2, .adds .x .x8 .x8 .x10, .adc .x .x9 .x9 .x12] ++
      ([ld .x3 di] ++ ([.adds .x .x3 .x3 .x8, .adc .x .x10 .x9 .x12] ++ [st .x3 di])) from rfl,
    WP.block_append_iff]
  have h12₁ : s₁.gpr .x12 = 0 := by rw [k₁.gpr _ (by decide), h12]
  refine WP.mono (mla4_ok s₁ (w := w) (hd := .x9) (by simp [hw8, hw9, hw10]) (Or.inl rfl) h12₁)
    fun s₂ ⟨e₂, k₂⟩ => ?_
  have hs₂ : Scr s₂ base size := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs₂ hdi hdi8 .x3) fun s₃ ⟨l₃, k₃, _⟩ => ?_
  have hs₃ : Scr s₃ base size := hs₂.of_keeps k₃ (by decide)
  have h12₃ : s₃.gpr .x12 = 0 := by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), h12₁]
  have x8₃ : s₃.gpr .x8 = s₂.gpr .x8 := k₃.gpr _ (by decide)
  have x9₃ : s₃.gpr .x9 = s₂.gpr .x9 := k₃.gpr _ (by decide)
  have hm₂ : s₂.mem = s.mem := by rw [k₂.mem, k₁.mem]
  have hw₁ : s₁.gpr w = s.gpr w := k₁.gpr _ (by simp [hw2])
  have hx10 : s₁.gpr .x10 = s.gpr .x10 := k₁.gpr _ (by decide)
  -- The bound: `dst_i + w src_i + h < 2^128`.
  have hbnd : (s₃.gpr .x3).toNat + (s₃.gpr .x8).toNat + 2 ^ 64 * (s₃.gpr .x9).toNat < 2 ^ 128 := by
    rw [x8₃, x9₃, Nat.add_assoc, e₂, l₃]
    have := (word s₂.mem base di).isLt
    have := (s₁.gpr .x10).isLt
    have hP : (s₁.gpr w).toNat * (s₁.gpr .x2).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
      Nat.mul_le_mul (by have := (s₁.gpr w).isLt; omega) (by have := (s₁.gpr .x2).isLt; omega)
    have : (2 ^ 64 - 1) * (2 ^ 64 - 1) = 2 ^ 128 - 2 ^ 65 + 1 := by decide
    omega
  rw [WP.block_append_iff]
  refine WP.mono (add2_ok s₃ h12₃ hbnd) fun s₄ ⟨e₄, k₄⟩ => ?_
  have hs₄ : Scr s₄ base size := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (st_ok hs₄ hdi hdi8 .x3) fun t et => ?_
  have mt : t.mem = s₄.mem.writeW (off base di) (s₄.gpr .x3) := by rw [et]
  have gt : t.gpr = s₄.gpr := by rw [et]
  have hm₄ : s₄.mem = s.mem := by rw [k₄.mem, k₃.mem, hm₂]
  refine ⟨?_, ⟨fun r hr => ?_, by rw [et]; exact k₄.rd.trans (k₃.rd.trans (k₂.rd.trans k₁.rd)),
    by rw [et]; exact k₄.wr.trans (k₃.wr.trans (k₂.wr.trans k₁.wr)),
    by rw [et]; exact k₄.sp.trans (k₃.sp.trans (k₂.sp.trans k₁.sp))⟩, ?_⟩
  · rw [mt, word_writeW_self, gt, e₄, x8₃, x9₃, Nat.add_assoc, e₂, l₃, hm₂, hw₁, l₁, hx10]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gt, k₄.gpr r (by simp [hr.2.1, hr.2.2.2.2]), k₃.gpr r (by simp [hr.2.1]),
      k₂.gpr r (by simp [hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]), k₁.gpr r (by simp [hr.1])]
  · rw [mt, hm₄]; exact writeW_outside _ _ _ (by omega)

/-- A row's words so far, and the next, accumulated. -/
theorem acc_arith {Wd A d x3 x10' x10 Dd wv xv Ws : Nat} (e₁ : Wd + A * x10 = Dd + wv * Ws)
    (e₃ : x3 + 2 ^ 64 * x10' = d + wv * xv + x10) :
    Wd + A * x3 + 2 ^ 64 * A * x10' = Dd + A * d + wv * (Ws + A * xv) := by
  have h : A * (x3 + 2 ^ 64 * x10') = A * (d + wv * xv + x10) := by rw [e₃]
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add] at h
  rw [Nat.mul_add, Nat.mul_left_comm wv A xv, Nat.mul_comm (2 ^ 64) A, Nat.mul_assoc A (2 ^ 64)]
  omega

/-- The words `0 … j` of `[dst] += w [src]` (from `x10 = 0`): `[dst]' + 2^(64 j) x10 = [dst] + w [src]`. -/
theorem mulAddRows_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {w : Reg}
    (hw : w ∉ [Reg.x0, .x2, .x3, .x8, .x9, .x10]) (h12 : s.gpr .x12 = 0) (h10 : s.gpr .x10 = 0)
    {dst src k : Nat} (hsrc : src + 8 * k ≤ size) (hs8 : src % 8 = 0) (hdst : dst + 8 * k ≤ size)
    (hd8 : dst % 8 = 0) (hsep : dst + 8 * k ≤ src ∨ src + 8 * k ≤ dst) :
    ∀ j, j ≤ k → WP isa (.block ((List.range j).flatMap (mulAddStep w dst src))) s fun t =>
      wordsVal t.mem base dst j + 2 ^ (64 * j) * (t.gpr .x10).toNat =
        wordsVal s.mem base dst j + (s.gpr w).toNat * wordsVal s.mem base src j ∧
      KeepRegs [.x2, .x3, .x8, .x9, .x10] s t ∧ Outside base dst (8 * j) s.mem t.mem
  | 0, _ => WP.block_nil ⟨by simp [wordsVal, h10], ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | j + 1, hj => by
    have hn := hs.nowrap
    have hw' := hw
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw
    obtain ⟨hw0, hw2, hw3, hw8, hw9, hw10⟩ := hw
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (mulAddRows_ok hs hw' h12 h10 hsrc hs8 hdst hd8 hsep j (by omega))
      fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have h12₁ : s₁.gpr .x12 = 0 := by rw [k₁.gpr _ (by decide), h12]
    refine WP.mono (mulAddStep_ok hs₁ hw' h12₁ (si := src + 8 * j) (di := dst + 8 * j) (by omega) (by omega)
      (by omega) (by omega)) fun t ⟨e₂, k₂, O₂⟩ => ?_
    have hw₁ : s₁.gpr w = s.gpr w := k₁.gpr _ (by simp [hw2, hw3, hw8, hw9, hw10])
    have hsrcj : word s₁.mem base (src + 8 * j) = word s.mem base (src + 8 * j) := word_out O₁ (by omega) (by omega)
    have hdstj : word s₁.mem base (dst + 8 * j) = word s.mem base (dst + 8 * j) := word_out O₁ (by omega) (by omega)
    refine ⟨?_, k₁.trans k₂, fun x hx => by rw [O₂ x (by omega), O₁ x (by omega)]⟩
    rw [wordsVal_succ_top, O₂.wordsVal (by omega) (by omega), wordsVal_succ_top s.mem base dst j,
      wordsVal_succ_top s.mem base src j, pow64_succ]
    rw [hw₁, hsrcj, hdstj] at e₂
    have := acc_arith e₁ e₂
    omega

/-- The carry's propagation through words `k + 1 … k + m` of `[dst]` (with `x12 = 0`). -/
theorem carries_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (h12 : s.gpr .x12 = 0)
    {dst k : Nat} (hd8 : dst % 8 = 0) :
    ∀ m, dst + 8 * (k + 1 + m) ≤ size → WP isa (.block ((List.range m).flatMap (carryStep dst k))) s fun t =>
      wordsVal t.mem base (dst + 8 * (k + 1)) m + 2 ^ (64 * m) * t.c.toNat =
        wordsVal s.mem base (dst + 8 * (k + 1)) m + s.c.toNat ∧
      KeepRegs [.x3] s t ∧ Outside base (dst + 8 * (k + 1)) (8 * m) s.mem t.mem
  | 0, _ => WP.block_nil ⟨by simp [wordsVal], ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | m + 1, hm => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (carries_ok hs h12 hd8 m (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have h12₁ : s₁.gpr .x12 = 0 := by rw [k₁.gpr _ (by decide), h12]
    rw [carryStep, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (ld_ok hs₁ (d := dst + 8 * (k + 1 + m)) (by omega) (by omega) .x3) fun s₂ ⟨l₂, k₂, c₂⟩ => ?_
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (addc_ok s₂ .x3 .x3 .x12 false (c := s₂.c) rfl) fun s₃ ⟨d₃, c₃, k₃⟩ => ?_
    have hs₃ : Scr s₃ base size := (hs₁.of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
    refine WP.mono (st_ok hs₃ (d := dst + 8 * (k + 1 + m)) (by omega) (by omega) .x3) fun t et => ?_
    have mt : t.mem = s₃.mem.writeW (off base (dst + 8 * (k + 1 + m))) (s₃.gpr .x3) := by rw [et]
    have ct : t.c = s₃.c := by rw [et]
    have hm₃ : s₃.mem = s₁.mem := by rw [k₃.mem, k₂.mem]
    have Oj := writeW_outside s₃.mem base (d := dst + 8 * (k + 1 + m)) (s₃.gpr .x3) (by omega)
    have h12₂ : s₂.gpr .x12 = 0 := by rw [k₂.gpr _ (by decide), h12₁]
    refine ⟨?_, (k₁.trans (Keeps.regs k₂)).trans ((Keeps.regs k₃).trans (by rw [et]; exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩)),
      fun x hx => by rw [mt, Oj x (by omega), hm₃, O₁ x (by omega)]⟩
    have hdj : word s₁.mem base (dst + 8 * (k + 1 + m)) = word s.mem base (dst + 8 * (k + 1 + m)) :=
      word_out O₁ (by omega) (by omega)
    have hv := VG.Proof.Ed25519.Word64.addCarry_value (s₂.gpr .x3) (s₂.gpr .x12) s₂.c
    rw [← d₃, ← c₃, h12₂, l₂, hdj] at hv
    have eo : dst + 8 * (k + 1) + 8 * m = dst + 8 * (k + 1 + m) := by omega
    rw [mt, ct, wordsVal_succ_top, eo, word_writeW_self, Oj.wordsVal (by omega) (by omega), hm₃,
      wordsVal_succ_top s.mem base (dst + 8 * (k + 1)) m, eo, pow64_succ]
    rw [c₂, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at hv
    have h : 2 ^ (64 * m) * ((s₃.gpr .x3).toNat + 2 ^ 64 * s₃.c.toNat) =
        2 ^ (64 * m) * ((word s.mem base (dst + 8 * (k + 1 + m))).toNat + s₁.c.toNat) := by rw [hv]
    rw [Nat.mul_add, Nat.mul_add] at h
    rw [Nat.mul_comm (2 ^ 64) (2 ^ (64 * m)), Nat.mul_assoc]
    omega

/-- `r = 0` by `movz`. -/
theorem movz0_ok' (s : State) (r : Reg) :
    WP isa (.block [.movz .x r 0 0]) s fun t => t.gpr r = 0 ∧ Keeps [r] s t ∧ t.c = s.c := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide,
    ite_true, RegUpd.gpr_write_self, Option.some.injEq, exists_eq_left']
  refine ⟨by decide, ⟨fun q hq => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  simp only [List.mem_singleton] at hq
  exact RegUpd.gpr_write_of_ne _ _ _ hq

/-- The arithmetic of `mulAdd`'s top: the rows, word `k`, then the carry through the rest. -/
theorem mulAdd_arith {W A Dk dk T h x3 c tl c' wS m : Nat} (e₁ : W + A * h = Dk + wS)
    (e₂ : x3 + 2 ^ 64 * c = dk + h) (e₃ : tl + 2 ^ (64 * m) * c' = T + c) :
    W + A * x3 + A * 2 ^ 64 * tl + A * 2 ^ 64 * 2 ^ (64 * m) * c' = Dk + A * dk + A * 2 ^ 64 * T + wS := by
  have h2 : A * (x3 + 2 ^ 64 * c) = A * (dk + h) := by rw [e₂]
  have h3 : A * 2 ^ 64 * (tl + 2 ^ (64 * m) * c') = A * 2 ^ 64 * (T + c) := by rw [e₃]
  rw [Nat.mul_add, Nat.mul_add] at h2 h3
  rw [← Nat.mul_assoc A (2 ^ 64) c] at h2
  rw [Nat.mul_assoc (A * 2 ^ 64) (2 ^ (64 * m)) c'] at *
  omega

/-- `[dst] += w [src] mod 2^(64 K)`. -/
theorem mulAdd_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {w : Reg}
    (hw : w ∉ [Reg.x0, .x2, .x3, .x8, .x9, .x10]) (h12 : s.gpr .x12 = 0) {dst src k K : Nat} (hkK : k ≤ K)
    (hsrc : src + 8 * k ≤ size) (hs8 : src % 8 = 0) (hdst : dst + 8 * K ≤ size) (hd8 : dst % 8 = 0)
    (hsep : dst + 8 * K ≤ src ∨ src + 8 * k ≤ dst) :
    WP isa (.block (mulAdd w dst src k K)) s fun t =>
      wordsVal t.mem base dst K = (wordsVal s.mem base dst K + (s.gpr w).toNat * wordsVal s.mem base src k) % 2 ^ (64 * K) ∧
      KeepRegs [.x2, .x3, .x8, .x9, .x10] s t ∧ Outside base dst (8 * K) s.mem t.mem := by
  have hn := hs.nowrap
  have hw' := hw
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw
  obtain ⟨hw0, hw2, hw3, hw8, hw9, hw10⟩ := hw
  rw [mulAdd, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (movz0_ok' s .x10) fun s₀ ⟨z₀, k₀, _⟩ => ?_
  have hs₀ := hs.of_keeps k₀ (by decide)
  have h12₀ : s₀.gpr .x12 = 0 := by rw [k₀.gpr _ (by decide), h12]
  have hw₀ : s₀.gpr w = s.gpr w := k₀.gpr _ (by simp [hw10])
  have hm₀ : s₀.mem = s.mem := k₀.mem
  refine WP.mono (mulAddRows_ok hs₀ hw' h12₀ z₀ hsrc hs8 (by omega) hd8 (by omega) k (Nat.le_refl _))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  rw [hw₀, hm₀] at e₁
  have hs₁ := hs₀.of_keepRegs k₁ (by decide)
  have h12₁ : s₁.gpr .x12 = 0 := by rw [k₁.gpr _ (by decide), h12₀]
  have k01 : KeepRegs [.x2, .x3, .x8, .x9, .x10] s s₁ :=
    ((Keeps.regs k₀).mono (by sub_regs)).trans (by rw [hm₀] at O₁; exact k₁)
  rw [hm₀] at O₁
  split
  · rename_i hk
    rw [WP.block_append_iff, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (ld_ok hs₁ (d := dst + 8 * k) (by omega) (by omega) .x3) fun s₂ ⟨l₂, k₂, _⟩ => ?_
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (addc_ok s₂ .x3 .x3 .x10 true (c := false) rfl) fun s₃ ⟨d₃, c₃, k₃⟩ => ?_
    have hs₃ : Scr s₃ base size := (hs₁.of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
    refine WP.mono (st_ok hs₃ (d := dst + 8 * k) (by omega) (by omega) .x3) fun s₄ e₄ => ?_
    have m₄ : s₄.mem = s₃.mem.writeW (off base (dst + 8 * k)) (s₃.gpr .x3) := by rw [e₄]
    have hs₄ : Scr s₄ base size := by rw [e₄]; exact ⟨hs₃.x0, hs₃.wr, hs₃.nowrap, hs₃.enc⟩
    have h12₄ : s₄.gpr .x12 = 0 := by
      rw [e₄]; exact (k₃.gpr _ (by decide)).trans ((k₂.gpr _ (by decide)).trans h12₁)
    refine WP.mono (carries_ok hs₄ h12₄ (dst := dst) (k := k) hd8 (K - k - 1) (by omega))
      fun t ⟨e₅, k₅, O₅⟩ => ?_
    have Ok := writeW_outside s₃.mem base (d := dst + 8 * k) (s₃.gpr .x3) (by omega)
    have hm₃ : s₃.mem = s₁.mem := by rw [k₃.mem, k₂.mem]
    have k34 : KeepRegs [.x2, .x3, .x8, .x9, .x10] s₁ s₄ :=
      (((Keeps.regs k₂).trans (Keeps.regs k₃)).trans (by rw [e₄]; exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩)).mono (by sub_regs)
    refine ⟨?_, (k01.trans k34).trans (k₅.mono (by sub_regs)),
      fun x hx => by rw [O₅ x (by omega), m₄, Ok x (by omega), hm₃, O₁ x (by omega)]⟩
    -- The value.
    have hv := VG.Proof.Ed25519.Word64.addCarry_value (s₂.gpr .x3) (s₂.gpr .x10) false
    rw [← d₃, ← c₃, l₂, show (false).toNat = 0 from rfl, Nat.add_zero, k₂.gpr .x10 (by decide)] at hv
    have hdk : word s₁.mem base (dst + 8 * k) = word s.mem base (dst + 8 * k) := word_out O₁ (by omega) (by omega)
    rw [hdk] at hv
    have hc₄ : s₄.c = s₃.c := by rw [e₄]
    rw [hc₄] at e₅
    have ht : wordsVal s₄.mem base (dst + 8 * (k + 1)) (K - k - 1) = wordsVal s.mem base (dst + 8 * (k + 1)) (K - k - 1) := by
      rw [m₄, Ok.wordsVal (by omega) (by omega), hm₃, O₁.wordsVal (by omega) (by omega)]
    rw [ht] at e₅
    have hK : K = k + 1 + (K - k - 1) := by omega
    have hlt := wordsVal_lt t.mem base dst K
    -- `[dst]' + 2^(64 K) c' = [dst] + w [src]`.
    have key : wordsVal t.mem base dst K + 2 ^ (64 * K) * t.c.toNat =
        wordsVal s.mem base dst K + (s.gpr w).toNat * wordsVal s.mem base src k := by
      rw [hK, wordsVal_split, wordsVal_split s.mem, wordsVal_succ_top, wordsVal_succ_top s.mem,
        O₅.word (by omega) (by omega), O₅.wordsVal (by omega) (by omega), m₄, word_writeW_self,
        Ok.wordsVal (by omega) (by omega), hm₃, show 64 * (k + 1) = 64 * k + 64 by omega,
        show 64 * (k + 1 + (K - k - 1)) = 64 * k + 64 + 64 * (K - k - 1) by omega, Nat.pow_add, Nat.pow_add]
      rw [Nat.pow_add (2 : Nat) (64 * k) 64]
      exact mulAdd_arith e₁ hv e₅
    rw [← key, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · rename_i hk
    obtain rfl : K = k := by omega
    refine WP.block_nil ⟨?_, k01, O₁⟩
    rw [← e₁, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wordsVal_lt _ _ _ _)]

/-- A mask: all ones or zero. -/
def IsMask (x : BitVec 64) : Prop := x = 0 ∨ x = BitVec.allOnes 64

/-- `[src] & m` word by word, as a number. -/
def masked (m : BitVec 64) (v : Nat) : Nat := if m = BitVec.allOnes 64 then v else 0

theorem and_mask {x m : BitVec 64} (hm : IsMask m) : (x &&& m).toNat = masked m x.toNat := by
  unfold masked
  rcases hm with rfl | rfl
  · simp only [show (0 : BitVec 64) ≠ BitVec.allOnes 64 by decide, ↓reduceIte]; simp
  · simp only [↓reduceIte, BitVec.and_allOnes]

/-- Word `i + 1` of `[dst] -= 2^64 ([src] & m)`: `d' + s + !c_in = d + 2^64 !c_out`. -/
theorem subShStep_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {m : Reg}
    (hm : m ∉ [Reg.x0, .x2, .x3]) (hmask : IsMask (s.gpr m)) {si di : Nat}
    (hsi : si + 8 ≤ size) (hsi8 : si % 8 = 0) (hdi : di + 8 ≤ size) (hdi8 : di % 8 = 0) {first c : Bool}
    (hc : (if first then true else s.c) = c) :
    WP isa (.block [ld .x3 di, ld .x2 si, .logic .and .x .x2 .x2 m,
      if first then .subs .x .x3 .x3 .x2 else .sbcs .x .x3 .x3 .x2, st .x3 di]) s fun t =>
      (word t.mem base di).toNat + masked (s.gpr m) (word s.mem base si).toNat + (!c).toNat =
        (word s.mem base di).toNat + 2 ^ 64 * (!t.c).toNat ∧
      KeepRegs [.x2, .x3] s t ∧ Outside base di 8 s.mem t.mem := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
  obtain ⟨hm0, hm2, hm3⟩ := hm
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ld_ok hs hdi hdi8 .x3) fun s₁ ⟨l₁, k₁, c₁⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ld_ok (hs.of_keeps k₁ (by decide)) hsi hsi8 .x2) fun s₂ ⟨l₂, k₂, c₂⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  have hand : WP isa (.block [.logic .and .x .x2 .x2 m]) s₂ fun t =>
      t.gpr .x2 = s₂.gpr .x2 &&& s₂.gpr m ∧ Keeps [.x2] s₂ t ∧ t.c = s₂.c := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
      BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
    simp only [List.mem_singleton] at hr
    exact RegUpd.gpr_write_of_ne _ _ _ hr
  refine WP.mono hand fun s₃ ⟨a₃, k₃, c₃⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  have hc₃ : (if first then true else s₃.c) = c := by rw [c₃, c₂, c₁, hc]
  refine WP.mono (subc_ok s₃ .x3 .x3 .x2 first hc₃) fun s₄ ⟨d₄, c₄, k₄⟩ => ?_
  have hs₄ : Scr s₄ base size :=
    (((hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)).of_keeps k₃ (by decide)).of_keeps k₄ (by decide)
  refine WP.mono (st_ok hs₄ hdi hdi8 .x3) fun t et => ?_
  have mt : t.mem = s₄.mem.writeW (off base di) (s₄.gpr .x3) := by rw [et]
  have gt : t.gpr = s₄.gpr := by rw [et]
  have ct : t.c = s₄.c := by rw [et]
  have hm₄ : s₄.mem = s.mem := by rw [k₄.mem, k₃.mem, k₂.mem, k₁.mem]
  have hmr : s₂.gpr m = s.gpr m := by rw [k₂.gpr _ (by simp [hm2]), k₁.gpr _ (by simp [hm3])]
  refine ⟨?_, ⟨fun r hr => ?_, by rw [et]; exact k₄.rd.trans (k₃.rd.trans (k₂.rd.trans k₁.rd)),
    by rw [et]; exact k₄.wr.trans (k₃.wr.trans (k₂.wr.trans k₁.wr)),
    by rw [et]; exact k₄.sp.trans (k₃.sp.trans (k₂.sp.trans k₁.sp))⟩, ?_⟩
  · have hb := sub_borrow (s₃.gpr .x3) (s₃.gpr .x2) c
    rw [← d₄, ← c₄] at hb
    rw [mt, word_writeW_self, ct]
    rw [a₃, and_mask (by rw [hmr]; exact hmask), hmr, l₂, k₁.mem] at hb
    rw [k₃.gpr .x3 (by decide), k₂.gpr .x3 (by decide), l₁] at hb
    exact hb
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gt, k₄.gpr r (by simp [hr.2]), k₃.gpr r (by simp [hr.1]), k₂.gpr r (by simp [hr.1]),
      k₁.gpr r (by simp [hr.2])]
  · rw [mt, hm₄]; exact writeW_outside _ _ _ (by omega)

theorem masked_add (m : BitVec 64) (a A b : Nat) : masked m (a + A * b) = masked m a + A * masked m b := by
  unfold masked; split <;> simp

/-- Words `1 … j` of `[dst] -= 2^64 ([src] & m)`: `V + S = D + 2^(64 j) !c`. -/
theorem subShRows_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {m : Reg}
    (hm : m ∉ [Reg.x0, .x2, .x3]) (hmask : IsMask (s.gpr m)) {dst src K : Nat}
    (hsrc : src + 8 * (K - 1) ≤ size) (hs8 : src % 8 = 0) (hdst : dst + 8 * K ≤ size) (hd8 : dst % 8 = 0)
    (hsep : dst + 8 * K ≤ src ∨ src + 8 * (K - 1) ≤ dst + 8) :
    ∀ j, 1 ≤ j → j ≤ K - 1 → WP isa (.block ((List.range j).flatMap (subShStep m dst src))) s fun t =>
      wordsVal t.mem base (dst + 8) j + masked (s.gpr m) (wordsVal s.mem base src j) =
        wordsVal s.mem base (dst + 8) j + 2 ^ (64 * j) * (!t.c).toNat ∧
      KeepRegs [.x2, .x3] s t ∧ Outside base (dst + 8) (8 * j) s.mem t.mem
  | 0, h, _ => absurd h (by decide)
  | j + 1, _, hj => by
    have hn := hs.nowrap
    have hm' := hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
    obtain ⟨hm0, hm2, hm3⟩ := hm
    rcases Nat.lt_or_ge j 1 with h0 | h1
    · obtain rfl : j = 0 := by omega
      rw [show (List.range (0 + 1)).flatMap (subShStep m dst src) =
        [ld .x3 (dst + 8), ld .x2 src, .logic .and .x .x2 .x2 m,
          if true then .subs .x .x3 .x3 .x2 else .sbcs .x .x3 .x3 .x2, st .x3 (dst + 8)] from by simp [subShStep]]
      refine WP.mono (subShStep_ok hs hm' hmask (si := src) (di := dst + 8) (by omega) hs8 (by omega) (by omega)
        (first := true) (c := true) rfl) fun t ⟨e, k, O⟩ => ⟨?_, k, ?_⟩
      · simp only [wordsVal, Nat.mul_zero, Nat.add_zero] at e ⊢
        simp only [Bool.not_true, Bool.toNat_false, Nat.add_zero] at e
        unfold masked at e ⊢; split <;> simp_all
      · simpa using O
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
      refine WP.mono (subShRows_ok hs hm' hmask hsrc hs8 hdst hd8 hsep j h1 (by omega))
        fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
      have hs₁ := hs.of_keepRegs k₁ (by decide)
      have hm₁ : s₁.gpr m = s.gpr m := k₁.gpr _ (by simp [hm2, hm3])
      rw [show subShStep m dst src j = [ld .x3 (dst + 8 * (j + 1)), ld .x2 (src + 8 * j), .logic .and .x .x2 .x2 m,
          if false then .subs .x .x3 .x3 .x2 else .sbcs .x .x3 .x3 .x2, st .x3 (dst + 8 * (j + 1))] from by
        simp [subShStep, show j ≠ 0 by omega]]
      refine WP.mono (subShStep_ok hs₁ hm' (by rw [hm₁]; exact hmask) (si := src + 8 * j) (di := dst + 8 * (j + 1))
        (by omega) (by omega) (by omega) (by omega) (first := false) (c := s₁.c) rfl) fun t ⟨e₂, k₂, O₂⟩ => ?_
      have hsrcj : word s₁.mem base (src + 8 * j) = word s.mem base (src + 8 * j) := word_out O₁ (by omega) (by omega)
      have hdstj : word s₁.mem base (dst + 8 * (j + 1)) = word s.mem base (dst + 8 * (j + 1)) :=
        word_out O₁ (by omega) (by omega)
      refine ⟨?_, k₁.trans k₂, fun x hx => by rw [O₂ x (by omega), O₁ x (by omega)]⟩
      have eo : dst + 8 + 8 * j = dst + 8 * (j + 1) := by omega
      rw [wordsVal_succ_top, eo, O₂.wordsVal (by omega) (by omega), wordsVal_succ_top s.mem base (dst + 8) j, eo,
        wordsVal_succ_top s.mem base src j, masked_add, pow64_succ]
      rw [hm₁, hsrcj, hdstj] at e₂
      generalize 2 ^ (64 * j) = A at *
      generalize (word t.mem base (dst + 8 * (j + 1))).toNat = v at *
      generalize masked (s.gpr m) (word s.mem base (src + 8 * j)).toNat = ms at *
      generalize (word s.mem base (dst + 8 * (j + 1))).toNat = d at *
      have h2 : A * (v + ms + (!s₁.c).toNat) = A * (d + 2 ^ 64 * (!t.c).toNat) := by rw [e₂]
      rw [Nat.mul_add A, Nat.mul_add A, Nat.mul_add A, Nat.mul_left_comm A (2 ^ 64)] at h2
      rw [Nat.mul_assoc (2 ^ 64) A]
      omega

/-- `[dst] -= 2^64 ([src] & m) mod 2^(64 K)`: `([dst]' + 2^64 S) mod 2^(64 K) = [dst]`. -/
theorem subSh_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {m : Reg}
    (hm : m ∉ [Reg.x0, .x2, .x3]) (hmask : IsMask (s.gpr m)) {dst src K : Nat} (hK : 2 ≤ K)
    (hsrc : src + 8 * (K - 1) ≤ size) (hs8 : src % 8 = 0) (hdst : dst + 8 * K ≤ size) (hd8 : dst % 8 = 0)
    (hsep : dst + 8 * K ≤ src ∨ src + 8 * (K - 1) ≤ dst + 8) :
    WP isa (.block (subSh m dst src K)) s fun t =>
      (wordsVal t.mem base dst K + 2 ^ 64 * masked (s.gpr m) (wordsVal s.mem base src (K - 1))) % 2 ^ (64 * K) =
        wordsVal s.mem base dst K ∧
      KeepRegs [.x2, .x3] s t ∧ Outside base dst (8 * K) s.mem t.mem := by
  have hn := hs.nowrap
  rw [subSh]
  refine WP.mono (subShRows_ok hs hm hmask hsrc hs8 hdst hd8 hsep (K - 1) (by omega) (Nat.le_refl _))
    fun t ⟨e, k, O⟩ => ⟨?_, k, fun x hx => O x (by omega)⟩
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at e ⊢
  have h0 : word t.mem base dst = word s.mem base dst := O.word (by omega) (by omega)
  rw [wordsVal, wordsVal, h0, pow64_succ]
  have hlt := wordsVal_lt s.mem base dst (K' + 1)
  rw [wordsVal, pow64_succ] at hlt
  have key : (word s.mem base dst).toNat + 2 ^ 64 * wordsVal t.mem base (dst + 8) K' +
      2 ^ 64 * masked (s.gpr m) (wordsVal s.mem base src K') =
      (word s.mem base dst).toNat + 2 ^ 64 * wordsVal s.mem base (dst + 8) K' +
      2 ^ 64 * 2 ^ (64 * K') * (!t.c).toNat := by
    have h := congrArg (2 ^ 64 * ·) e
    simp only [Nat.mul_add] at h
    rw [Nat.mul_assoc]; omega
  rw [key, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-! ## The arithmetic shift by 59 -/

theorem extr59_toNat (hi lo : BitVec 64) :
    ((hi ++ lo).extractLsb' 59 64).toNat = (lo.toNat / 2 ^ 59 + 2 ^ 5 * hi.toNat) % 2 ^ 64 := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := lo.isLt; have := hi.isLt
  omega

/-- `d = (hi:lo) >> 59`. -/
theorem extr59_ok (s : State) (d hi lo : Reg) :
    WP isa (.block [.extr .x d hi lo 59]) s fun t =>
      (t.gpr d).toNat = ((s.gpr lo).toNat / 2 ^ 59 + 2 ^ 5 * (s.gpr hi).toNat) % 2 ^ 64 ∧
      Keeps [d] s t ∧ t.c = s.c := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_extr (show 59 < Size.x.bits by decide), read_x,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨extr59_toNat _ _, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

/-- A word's sign, as a word: all ones if its top bit is set. -/
def sgnW (x : BitVec 64) : Nat := if 2 ^ 63 ≤ x.toNat then 2 ^ 64 - 1 else 0

/-- `d = ` the sign of `r`, as a mask. -/
theorem maskOf_ok (s : State) {d r : Reg} (h12 : s.gpr .x12 = 0) (hd : Reg.x12 ≠ d) :
    WP isa (.block (maskOf d r)) s fun t =>
      (t.gpr d).toNat = sgnW (s.gpr r) ∧ IsMask (t.gpr d) ∧ Keeps [d] s t ∧ t.c = s.c := by
  apply WP.of_runBlock
  simp only [maskOf, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
    BitVec.setWidth_eq, ↓reduceIte, show 63 < Size.x.bits from by decide,
    Option.some.injEq, exists_eq_left', hd, h12]
  have hv : ((0 : BitVec 64) - s.gpr r >>> 63).toNat = sgnW (s.gpr r) := by
    rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := (s.gpr r).isLt
    unfold sgnW; split <;> simp <;> omega
  refine ⟨hv, ?_, ⟨fun r' hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  · unfold sgnW at hv; split at hv
    · exact Or.inr (BitVec.eq_of_toNat_eq (by rw [hv, BitVec.toNat_allOnes]))
    · exact Or.inl (BitVec.eq_of_toNat_eq (by rw [hv]; rfl))
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ↓reduceIte]

/-- `x9 = ` the sign of `x3`, as a mask. -/
theorem sgnMask_ok (s : State) (h12 : s.gpr .x12 = 0) :
    WP isa (.block sgnMask) s fun t =>
      (t.gpr .x9).toNat = sgnW (s.gpr .x3) ∧ IsMask (t.gpr .x9) ∧ Keeps [.x9] s t ∧ t.c = s.c :=
  maskOf_ok s h12 (by decide)

/-- Words `0 … j` of `X / 2^59`: from word `j` of `X`, and the next. -/
theorem shr_arith (j V s t : Nat) (hV : V < 2 ^ (64 * j)) :
    ((V + 2 ^ (64 * j) * s + 2 ^ (64 * j) * 2 ^ 64 * t) / 2 ^ 59) % (2 ^ (64 * j) * 2 ^ 64) =
      ((V + 2 ^ (64 * j) * s) / 2 ^ 59) % 2 ^ (64 * j) + 2 ^ (64 * j) * ((s / 2 ^ 59 + 2 ^ 5 * t) % 2 ^ 64) := by
  generalize 2 ^ (64 * j) = A at *
  have hA0 : 0 < A := by omega
  have e1 : A * 2 ^ 64 * t = 2 ^ 59 * (A * (2 ^ 5 * t)) := by
    rw [show (2 : Nat) ^ 64 = 2 ^ 59 * 2 ^ 5 from rfl, Nat.mul_comm A, Nat.mul_assoc, Nat.mul_assoc,
      Nat.mul_left_comm A]
  have e2 : (V + A * s) / A = s := by
    rw [Nat.add_mul_div_left _ _ hA0, Nat.div_eq_of_lt hV, Nat.zero_add]
  rw [e1, Nat.add_mul_div_left _ _ (by decide), Nat.mod_mul, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ hA0, Nat.div_div_eq_div_mul, Nat.mul_comm (2 ^ 59), ← Nat.div_div_eq_div_mul, e2]

/-- Words `0 … j - 1` of `[src] >> 59` (`j + 1 ≤ L` words of `[src]`). -/
theorem shrRows_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {dst src L : Nat}
    (hsrc : src + 8 * L ≤ size) (hs8 : src % 8 = 0) (hdst : dst + 8 * L ≤ size) (hd8 : dst % 8 = 0)
    (hsep : dst + 8 * L ≤ src ∨ src + 8 * L ≤ dst) :
    ∀ j, j + 1 ≤ L → WP isa (.block ((List.range j).flatMap (shrStep dst src))) s fun t =>
      wordsVal t.mem base dst j = (wordsVal s.mem base src (j + 1) / 2 ^ 59) % 2 ^ (64 * j) ∧
      KeepRegs [.x2, .x3, .x8] s t ∧ Outside base dst (8 * j) s.mem t.mem
  | 0, _ => WP.block_nil ⟨by simp only [wordsVal, Nat.mul_zero, Nat.pow_zero, Nat.mod_one],
    ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | j + 1, hj => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (shrRows_ok hs hsrc hs8 hdst hd8 hsep j (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    rw [shrStep, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (ld_ok hs₁ (d := src + 8 * j) (by omega) (by omega) .x2) fun s₂ ⟨l₂, k₂, _⟩ => ?_
    have hs₂ := hs₁.of_keeps k₂ (by decide)
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (ld_ok hs₂ (d := src + 8 * (j + 1)) (by omega) (by omega) .x3) fun s₃ ⟨l₃, k₃, _⟩ => ?_
    have hs₃ := hs₂.of_keeps k₃ (by decide)
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (extr59_ok s₃ .x8 .x3 .x2) fun s₄ ⟨x₄, k₄, _⟩ => ?_
    have hs₄ := hs₃.of_keeps k₄ (by decide)
    refine WP.mono (st_ok hs₄ (d := dst + 8 * j) (by omega) (by omega) .x8) fun t et => ?_
    have mt : t.mem = s₄.mem.writeW (off base (dst + 8 * j)) (s₄.gpr .x8) := by rw [et]
    have gt : t.gpr = s₄.gpr := by rw [et]
    have hm₄ : s₄.mem = s₁.mem := by rw [k₄.mem, k₃.mem, k₂.mem]
    have Oj := writeW_outside s₄.mem base (d := dst + 8 * j) (s₄.gpr .x8) (by omega)
    have w₂ : word s₁.mem base (src + 8 * j) = word s.mem base (src + 8 * j) := word_out O₁ (by omega) (by omega)
    have w₃ : word s₂.mem base (src + 8 * (j + 1)) = word s.mem base (src + 8 * (j + 1)) := by
      rw [k₂.mem]; exact word_out O₁ (by omega) (by omega)
    have hx2 : s₃.gpr .x2 = s₂.gpr .x2 := k₃.gpr _ (by decide)
    refine ⟨?_, ⟨fun r hr => ?_, by rw [et]; exact k₄.rd.trans (k₃.rd.trans (k₂.rd.trans k₁.rd)),
      by rw [et]; exact k₄.wr.trans (k₃.wr.trans (k₂.wr.trans k₁.wr)),
      by rw [et]; exact k₄.sp.trans (k₃.sp.trans (k₂.sp.trans k₁.sp))⟩,
      fun x hx => by rw [mt, Oj x (by omega), hm₄, O₁ x (by omega)]⟩
    · rw [mt, wordsVal_succ_top, word_writeW_self, Oj.wordsVal (by omega) (by omega), hm₄, e₁, x₄, hx2, l₂, l₃,
        w₂, w₃, wordsVal_succ_top s.mem base src (j + 1), wordsVal_succ_top s.mem base src j, pow64_succ,
        Nat.mul_comm (2 ^ 64) (2 ^ (64 * j))]
      exact (shr_arith j _ _ _ (wordsVal_lt _ _ _ _)).symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [gt, k₄.gpr r (by simp [hr.2.2]), k₃.gpr r (by simp [hr.2.1]), k₂.gpr r (by simp [hr.1]),
        k₁.gpr r (by simp [hr.1, hr.2.1, hr.2.2])]

/-- `[src]` (`L` words) sign-extended by a word. -/
def sext (m : Mem) (base : Addr) (src L : Nat) : Nat :=
  wordsVal m base src L + 2 ^ (64 * L) * sgnW (word m base (src + 8 * (L - 1)))

/-- `[dst] = [src] >> 59`, arithmetic (`L ≥ 1` words). -/
theorem shr59_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (h12 : s.gpr .x12 = 0)
    {dst src L : Nat} (hL : 1 ≤ L)
    (hsrc : src + 8 * L ≤ size) (hs8 : src % 8 = 0) (hdst : dst + 8 * L ≤ size) (hd8 : dst % 8 = 0)
    (hsep : dst + 8 * L ≤ src ∨ src + 8 * L ≤ dst) :
    WP isa (.block (shr59 dst src L)) s fun t =>
      wordsVal t.mem base dst L = (sext s.mem base src L / 2 ^ 59) % 2 ^ (64 * L) ∧
      KeepRegs [.x2, .x3, .x8, .x9] s t ∧ Outside base dst (8 * L) s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨j, rfl⟩ : ∃ j, L = j + 1 := ⟨L - 1, by omega⟩
  simp only [shr59, Nat.add_sub_cancel]
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (shrRows_ok hs hsrc hs8 hdst hd8 hsep j (Nat.le_refl _)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs₁ (d := src + 8 * j) (by omega) (by omega) .x3) fun s₂ ⟨l₂, k₂, _⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sgnMask_ok s₂ (by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), h12]))
    fun s₃ ⟨g₃, _, k₃, _⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (extr59_ok s₃ .x8 .x9 .x3) fun s₄ ⟨x₄, k₄, _⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (st_ok hs₄ (d := dst + 8 * j) (by omega) (by omega) .x8) fun t et => ?_
  have mt : t.mem = s₄.mem.writeW (off base (dst + 8 * j)) (s₄.gpr .x8) := by rw [et]
  have gt : t.gpr = s₄.gpr := by rw [et]
  have hm₄ : s₄.mem = s₁.mem := by rw [k₄.mem, k₃.mem, k₂.mem]
  have Oj := writeW_outside s₄.mem base (d := dst + 8 * j) (s₄.gpr .x8) (by omega)
  have w₂ : word s₁.mem base (src + 8 * j) = word s.mem base (src + 8 * j) := word_out O₁ (by omega) (by omega)
  have hx3 : s₃.gpr .x3 = s₂.gpr .x3 := k₃.gpr _ (by decide)
  refine ⟨?_, ⟨fun r hr => ?_, by rw [et]; exact k₄.rd.trans (k₃.rd.trans (k₂.rd.trans k₁.rd)),
    by rw [et]; exact k₄.wr.trans (k₃.wr.trans (k₂.wr.trans k₁.wr)),
    by rw [et]; exact k₄.sp.trans (k₃.sp.trans (k₂.sp.trans k₁.sp))⟩,
    fun x hx => by rw [mt, Oj x (by omega), hm₄, O₁ x (by omega)]⟩
  · rw [mt, wordsVal_succ_top, word_writeW_self, Oj.wordsVal (by omega) (by omega), hm₄, e₁, x₄, g₃, hx3, l₂,
      w₂, sext, Nat.add_sub_cancel, wordsVal_succ_top s.mem base src j, pow64_succ,
      Nat.mul_comm (2 ^ 64) (2 ^ (64 * j))]
    exact (shr_arith j _ _ _ (wordsVal_lt _ _ _ _)).symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gt, k₄.gpr r (by simp [hr.2.2.1]), k₃.gpr r (by simp [hr.2.2.2]), k₂.gpr r (by simp [hr.2.1]),
      k₁.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1])]

/-- `[dst] = [src]` (`k` words). -/
theorem copyW_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {dst src : Nat}
    (hs8 : src % 8 = 0) (hd8 : dst % 8 = 0) : ∀ k, src + 8 * k ≤ size → dst + 8 * k ≤ size →
    (dst + 8 * k ≤ src ∨ src + 8 * k ≤ dst) →
    WP isa (.block (copyW dst src k)) s fun t =>
      wordsVal t.mem base dst k = wordsVal s.mem base src k ∧
      KeepRegs [.x2] s t ∧ Outside base dst (8 * k) s.mem t.mem
  | 0, _, _, _ => WP.block_nil ⟨rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | k + 1, hsrc, hdst, hsep => by
    have hn := hs.nowrap
    rw [copyW, List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copyW_ok hs hs8 hd8 k (by omega) (by omega) (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    rw [copyStep, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (ld_ok hs₁ (d := src + 8 * k) (by omega) (by omega) .x2) fun s₂ ⟨l₂, k₂, _⟩ => ?_
    refine WP.mono (st_ok (hs₁.of_keeps k₂ (by decide)) (d := dst + 8 * k) (by omega) (by omega) .x2)
      fun t et => ?_
    have mt : t.mem = s₂.mem.writeW (off base (dst + 8 * k)) (s₂.gpr .x2) := by rw [et]
    have gt : t.gpr = s₂.gpr := by rw [et]
    have Oj := writeW_outside s₂.mem base (d := dst + 8 * k) (s₂.gpr .x2) (by omega)
    refine ⟨?_, ⟨fun r hr => ?_, by rw [et]; exact k₂.rd.trans k₁.rd, by rw [et]; exact k₂.wr.trans k₁.wr,
      by rw [et]; exact k₂.sp.trans k₁.sp⟩, fun x hx => by rw [mt, Oj x (by omega), k₂.mem, O₁ x (by omega)]⟩
    · rw [mt, wordsVal_succ_top, word_writeW_self, Oj.wordsVal (by omega) (by omega), k₂.mem, e₁, l₂,
        word_out O₁ (by omega) (by omega), wordsVal_succ_top s.mem base src k]
    · simp only [List.mem_singleton] at hr
      rw [gt, k₂.gpr r (by simp [hr]), k₁.gpr r (by simp [hr])]

/-! ## Linear combinations -/

/-- `[T] = w [x] + w' [y] - 2^64 (([x] & mw) + ([y] & mw')) mod 2^(64 K)`, for words `w`, `w'`
and masks `mw`, `mw'` (`[x]`, `[y]` of `k` words, `K - 1 ≤ k ≤ K`). -/
theorem lin_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {w w' mw mw' : Reg}
    (hw : w ∉ [Reg.x0, .x2, .x3, .x8, .x9, .x10]) (hw' : w' ∉ [Reg.x0, .x2, .x3, .x8, .x9, .x10])
    (hmw : mw ∉ [Reg.x0, .x2, .x3, .x8, .x9, .x10]) (hmw' : mw' ∉ [Reg.x0, .x2, .x3, .x8, .x9, .x10])
    (hm : IsMask (s.gpr mw)) (hm' : IsMask (s.gpr mw')) (h12 : s.gpr .x12 = 0)
    {T x y k K : Nat} (h1 : 1 ≤ k) (hkK : k ≤ K) (hK : 2 ≤ K) (hk' : K ≤ k + 1)
    (hx : x + 8 * k ≤ size) (hx8 : x % 8 = 0) (hy : y + 8 * k ≤ size) (hy8 : y % 8 = 0)
    (hT : T + 8 * K ≤ size) (hT8 : T % 8 = 0)
    (hTx : T + 8 * K ≤ x ∨ x + 8 * k ≤ T) (hTy : T + 8 * K ≤ y ∨ y + 8 * k ≤ T) :
    WP isa (.block (lin w w' mw mw' T x y k K)) s fun t =>
      (wordsVal t.mem base T K + 2 ^ 64 * (masked (s.gpr mw) (wordsVal s.mem base x (K - 1)) +
        masked (s.gpr mw') (wordsVal s.mem base y (K - 1)))) % 2 ^ (64 * K) =
      ((s.gpr w).toNat * wordsVal s.mem base x k + (s.gpr w').toNat * wordsVal s.mem base y k) % 2 ^ (64 * K) ∧
      KeepRegs [.x2, .x3, .x8, .x9, .x10] s t ∧ Outside base T (8 * K) s.mem t.mem := by
  have hn := hs.nowrap
  have nk : ∀ r, r ∉ [Reg.x0, .x2, .x3, .x8, .x9, .x10] → r ∉ [Reg.x2, .x3, .x8, .x9, .x10] :=
    fun r h h' => h (List.mem_cons_of_mem _ h')
  have hw'₀ := nk _ hw'; have hw'A := hw'
  have hmw₀ := nk _ hmw; have hmw'₀ := nk _ hmw'
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw hw' hmw hmw'
  simp only [lin, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (mulw_ok hs (w := w) (by simp [hw.1, hw.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2]) h12 h1 hkK
    hx hx8 hT hT8 hTx) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have g₁ : ∀ r ∉ [Reg.x2, .x3, .x8, .x9, .x10], s₁.gpr r = s.gpr r :=
    (k₁.mono (by decide)).gpr
  rw [WP.block_append_iff]
  refine WP.mono (mulAdd_ok hs₁ hw'A (by rw [g₁ _ (by decide), h12]) hkK hy hy8 hT hT8 hTy)
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have hK1 : K - 1 ≤ k := by omega
  rw [WP.block_append_iff]
  refine WP.mono (subSh_ok hs₂ (m := mw) (by simp [hmw.1, hmw.2.1, hmw.2.2.1])
    (by rw [k₂.gpr _ hmw₀, g₁ _ hmw₀]; exact hm) hK (by omega) hx8 hT hT8 (by omega)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  refine WP.mono (subSh_ok hs₃ (m := mw') (by simp [hmw'.1, hmw'.2.1, hmw'.2.2.1])
    (by rw [k₃.gpr _ (by simp [hmw'.2.1, hmw'.2.2.1]), k₂.gpr _ hmw'₀, g₁ _ hmw'₀]; exact hm') hK (by omega)
    hy8 hT hT8 (by omega)) fun t ⟨e₄, k₄, O₄⟩ => ?_
  refine ⟨?_, ((k₁.mono (by decide)).trans k₂).trans ((k₃.trans k₄).mono (by decide)),
    (O₁.trans O₂).trans (O₃.trans O₄)⟩
  -- The registers and inputs, at each step.
  rw [k₃.gpr _ (by simp [hmw'.2.1, hmw'.2.2.1]), k₂.gpr _ hmw'₀, g₁ _ hmw'₀,
    O₃.wordsVal (by omega) (by omega), O₂.wordsVal (by omega) (by omega), O₁.wordsVal (by omega) (by omega)] at e₄
  rw [k₂.gpr _ hmw₀, g₁ _ hmw₀, O₂.wordsVal (by omega) (by omega), O₁.wordsVal (by omega) (by omega)] at e₃
  rw [e₁, g₁ _ hw'₀, O₁.wordsVal (by omega) (by omega)] at e₂
  generalize 2 ^ (64 * K) = M at *
  generalize masked (s.gpr mw) (wordsVal s.mem base x (K - 1)) = a at *
  generalize masked (s.gpr mw') (wordsVal s.mem base y (K - 1)) = b at *
  rw [show wordsVal t.mem base T K + 2 ^ 64 * (a + b) = (wordsVal t.mem base T K + 2 ^ 64 * b) + 2 ^ 64 * a by
    rw [Nat.mul_add]; omega, ← Nat.mod_add_mod, e₄, e₃, e₂, Nat.mod_add_mod]

end VG.Proof.Weierstrass.AArch64
