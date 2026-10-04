import VerifiedGarbage.Proof.Weierstrass.AArch64.CombSelect
import VerifiedGarbage.Impl.Weierstrass.AArch64.Window

/-!
# The window method on AArch64: the constant-time selection

With `maskReg m` all ones exactly for `m = a` (`a ≤ 8`), `selectWord` loads
word `w` of the coordinate of every entry `[m]P` of the table, ANDs it with
its mask and ORs it into `x4`, so that the word of `[a]P` survives
(`winSelectWord_ok`); `select` writes the entry's `X`, `Y` and `Z`
(`select_ok`): `(0 : R : 0)` for `a = 0`, else `[a]P`'s coordinates.
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- Numbers whose words are the same. -/
theorem wordsVal_of_words (m m' : Mem) (base : Addr) : ∀ (o o' n : Nat),
    (∀ j < n, word m' base (o + 8 * j) = word m base (o' + 8 * j)) →
    wordsVal m' base o n = wordsVal m base o' n
  | _, _, 0, _ => rfl
  | o, o', n + 1, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    rw [wordsVal, wordsVal, h0, wordsVal_of_words m m' base (o + 8) (o' + 8) n fun j hj => by
      rw [show o + 8 + 8 * j = o + 8 * (j + 1) by omega, show o' + 8 + 8 * j = o' + 8 * (j + 1) by omega]
      exact h (j + 1) (by omega)]

/-- `x4 |= [d] & mask m`. -/
theorem loadCand_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d m : Nat}
    (hd : d + 8 ≤ size) (hd8 : d % 8 = 0) (hm : m ≤ 8) :
    WP isa (.block (WinCfg.loadCand d m)) s fun t =>
      t.gpr .x4 = s.gpr .x4 ||| (word s.mem base d &&& s.gpr (maskReg m)) ∧ Keeps [.x2, .x4, .x9] s t := by
  have hr := maskRegs_not m hm
  rw [WinCfg.loadCand, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ld_ok hs hd hd8 .x9) fun a ⟨a9, ka, _⟩ => ?_
  have am : a.gpr (maskReg m) = s.gpr (maskReg m) := ka.gpr _ (by simpa using hr.2.2.1)
  have a4 : a.gpr .x4 = s.gpr .x4 := ka.gpr _ (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, a9, am, a4,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ⟨fun r hr' => ?_, ka.mem, ka.rd, ka.wr, ka.sp⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
  simp only [RegUpd.gpr_write, hr'.1, hr'.2.1, ite_false]
  exact ka.gpr _ (by simpa using hr'.2.2)

/-- The word of magnitude `a`: `z` for `0`, else `f (a - 1)`. -/
def selW (z : BitVec 64) (f : Nat → BitVec 64) (a : Nat) : BitVec 64 := if a = 0 then z else f (a - 1)

/-- The candidates `1 … i` ORed into `x4`, word `w` of the coordinate at
`d m` of `[m + 1]P`. -/
theorem loadCands_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (ha : a ≤ 8) (hM : MasksOf s a) {X₀ : BitVec 64} (h4 : s.gpr .x4 = X₀) (d : Nat → Nat)
    (hd : ∀ i < 8, d i + 8 ≤ size ∧ d i % 8 = 0) :
    WP isa (.block ((List.range 8).flatMap fun i => WinCfg.loadCand (d i) (i + 1))) s fun t =>
      t.gpr .x4 = X₀ ||| (if 1 ≤ a then word s.mem base (d (a - 1)) else 0) ∧
        Keeps [.x2, .x4, .x9] s t := by
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8)
    (fun k t => t.gpr .x4 = X₀ ||| (if 1 ≤ a ∧ a ≤ k then word s.mem base (d (a - 1)) else 0) ∧
      Keeps [.x2, .x4, .x9] s t) (fun k t hk ⟨t4, kt⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨by rw [h4]; simp [show ¬(1 ≤ a ∧ a = 0) by omega], ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩)
    fun t ⟨t4, kt⟩ => ⟨by rw [t4]; congr 1; by_cases h : 1 ≤ a <;> simp [h, ha], kt⟩
  have ht := hs.of_keeps kt (by decide)
  refine WP.mono (loadCand_ok ht (d := d k) (m := k + 1) (hd k hk).1 (hd k hk).2 (by omega))
    fun u ⟨u4, ku⟩ => ⟨?_, kt.trans ku⟩
  rw [u4, t4, (hM.keep kt) (k + 1) (by omega), bmask_and, BitVec.or_assoc, kt.mem]
  congr 1
  by_cases h1 : a = k + 1
  · subst h1
    simp [show ¬(k + 1 ≤ k) by omega]
  · by_cases h2 : 1 ≤ a ∧ a ≤ k
    · simp [h1, h2, show 1 ≤ a ∧ a ≤ k + 1 by omega]
    · simp [h1, h2, show ¬(1 ≤ a ∧ a ≤ k + 1) by omega]

/-- The table's slot of coordinate `c` of `[i + 1]P`. -/
def tblSlot (K : WinCfg) (c i : Nat) : Nat := K.tbl + 24 * K.M.n * i + 8 * K.M.n * c

theorem winSelectWord_eq (K : WinCfg) (c o w : Nat) : WinCfg.selectWord K c o w =
    ([.movz .x .x4 0 0] : List Instr) ++ ((if c = 1 then const64 .x9 (wordOf K.one w) ++
      ([.logic .and .x .x4 .x9 (maskReg 0)] : List Instr) else []) ++
      ((List.range 8).flatMap (fun i => WinCfg.loadCand (tblSlot K c i + 8 * w) (i + 1)) ++
        ([st .x4 (o + 8 * w)] : List Instr))) := by
  simp only [WinCfg.selectWord, tblSlot, List.append_assoc]

/-- `Y`'s word of `O`, `R mod p`'s, or zero. -/
def zW (K : WinCfg) (c w : Nat) : BitVec 64 := if c = 1 then wordOf K.one w else 0

/-- Word `w` of coordinate `c` of the magnitude's entry, into `[o + 8 w]`. -/
theorem winSelectWord_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (K : WinCfg)
    {a : Nat} (ha : a ≤ 8) (hM : MasksOf s a) {c o w : Nat} (ho : o + 8 * w + 8 ≤ size)
    (ho8 : o % 8 = 0) (hd : ∀ i < 8, tblSlot K c i + 8 * w + 8 ≤ size ∧ tblSlot K c i % 8 = 0) :
    WP isa (.block (WinCfg.selectWord K c o w)) s fun t =>
      t.mem = s.mem.writeW (off base (o + 8 * w))
        (selW (zW K c w) (fun i => word s.mem base (tblSlot K c i + 8 * w)) a) ∧
      KeepRegs [.x2, .x4, .x9] s t := by
  rw [winSelectWord_eq, WP.block_append_iff]
  refine WP.mono (movz0_ok s .x4) fun s₁ ⟨z₁, k₁⟩ => ?_
  have hM₁ := hM.keep (k₁.mono (by decide))
  rw [WP.block_append_iff]
  have hopt : WP isa (.block (if c = 1 then const64 .x9 (wordOf K.one w) ++
      ([.logic .and .x .x4 .x9 (maskReg 0)] : List Instr) else [])) s₁ fun t =>
      t.gpr .x4 = (if a = 0 then zW K c w else 0) ∧ Keeps [.x2, .x4, .x9] s₁ t := by
    split
    · rename_i hc
      rw [WP.block_append_iff]
      refine WP.mono (const64_ok s₁ .x9 _) fun t ⟨t9, kt⟩ => ?_
      have tm : t.gpr (maskReg 0) = bmask (decide (a = 0)) := by
        rw [kt.gpr _ (by decide)]; exact hM₁ 0 (by decide)
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
        BitVec.setWidth_eq, t9, tm, bmask_and, Option.some.injEq, exists_eq_left']
      refine ⟨by by_cases h : a = 0 <;> simp [h, zW, hc], ⟨fun r hr => ?_, kt.mem, kt.rd, kt.wr, kt.sp⟩⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.2.1, ite_false]
      exact kt.gpr _ (by simpa using hr.2.2)
    · rename_i hc
      exact WP.block_nil ⟨by rw [z₁]; simp [zW, hc], ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩
  refine WP.mono hopt fun s₂ ⟨x₂, k₂⟩ => ?_
  have hM₂ := hM₁.keep k₂
  have hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loadCands_ok hs₂ ha hM₂ x₂ (fun i => tblSlot K c i + 8 * w) fun i hi =>
      ⟨(hd i hi).1, by have := (hd i hi).2; omega⟩) fun s₃ ⟨x₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (st_out hs₃ (o := o + 8 * w) ho (by omega) .x4) fun t ⟨m, kt, _⟩ => ⟨?_, ?_⟩
  · rw [m, x₃, k₃.mem, k₂.mem, k₁.mem]
    congr 1
    unfold selW
    by_cases h : a = 0
    · subst h; simp
    · simp [h, show 1 ≤ a by omega]
  · exact (((Keeps.regs k₁).mono (by decide)).trans ((Keeps.regs (k₂.trans k₃)))).trans
      (kt.mono (by decide))

/-- The `k` words of coordinate `c` of the magnitude's entry, into `[o]`, the
table's slots apart from `[o]`. -/
theorem winSelectWords_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (K : WinCfg)
    {a : Nat} (ha : a ≤ 8) (hM : MasksOf s a) {c o : Nat} (ho8 : o % 8 = 0) :
    ∀ k, o + 8 * k ≤ size → k ≤ K.M.n →
    (∀ i < 8, tblSlot K c i + 8 * K.M.n ≤ size ∧ tblSlot K c i % 8 = 0 ∧
      (tblSlot K c i + 8 * K.M.n ≤ o ∨ o + 8 * K.M.n ≤ tblSlot K c i)) →
    WP isa (.block ((List.range k).flatMap (WinCfg.selectWord K c o))) s fun t =>
      (∀ w < k, word t.mem base (o + 8 * w) =
        selW (zW K c w) (fun i => word s.mem base (tblSlot K c i + 8 * w)) a) ∧
      KeepRegs [.x2, .x4, .x9] s t ∧ Outside base o (8 * k) s.mem t.mem
  | 0, _, _, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, hk, hkn, hd => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (winSelectWords_ok hs K ha hM ho8 k (by omega) (by omega) hd) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    refine WP.mono (winSelectWord_ok hs₁ K ha (hM.keepRegs k₁) (c := c) (w := k) (by omega) ho8
      fun i hi => ⟨by have := (hd i hi).1; omega, (hd i hi).2.1⟩) fun s₂ ⟨m₂, k₂⟩ => ?_
    have O₂ : Outside base (o + 8 * k) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.word (by omega) (by omega), e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₂, word_writeW_self]
      unfold selW
      split
      · rfl
      · have hi : a - 1 < 8 := by omega
        have := hd (a - 1) hi
        exact O₁.word (by omega) (by rcases this.2.2 with h | h <;> omega)

/-- Coordinate `c` of the magnitude's entry, as a number: `z` for `0`. -/
theorem selectCoord_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (K : WinCfg)
    {a : Nat} (ha : a ≤ 8) (hM : MasksOf s a) {c o : Nat} (ho8 : o % 8 = 0) (ho : o + 8 * K.M.n ≤ size)
    (hd : ∀ i < 8, tblSlot K c i + 8 * K.M.n ≤ size ∧ tblSlot K c i % 8 = 0 ∧
      (tblSlot K c i + 8 * K.M.n ≤ o ∨ o + 8 * K.M.n ≤ tblSlot K c i))
    (h1 : K.one < 2 ^ (64 * K.M.n)) :
    WP isa (.block ((List.range K.M.n).flatMap (WinCfg.selectWord K c o))) s fun t =>
      wordsVal t.mem base o K.M.n =
        (if a = 0 then (if c = 1 then K.one else 0) else wordsVal s.mem base (tblSlot K c (a - 1)) K.M.n) ∧
      KeepRegs [.x2, .x4, .x9] s t ∧ Outside base o (8 * K.M.n) s.mem t.mem := by
  refine WP.mono (winSelectWords_ok hs K ha hM ho8 K.M.n ho (Nat.le_refl _) hd) fun t ⟨e, k, O⟩ =>
    ⟨?_, k, O⟩
  by_cases h0 : a = 0
  · simp only [h0, ↓reduceIte]
    refine wordsVal_of_shifts _ _ _ _ _ (by split <;> omega) fun j hj => ?_
    rw [e j hj]
    by_cases hc : c = 1 <;> simp [selW, zW, h0, hc, wordOf]
  · simp only [h0, ↓reduceIte]
    refine wordsVal_of_words _ _ _ _ _ _ fun j hj => ?_
    rw [e j hj]
    simp only [selW, h0, ↓reduceIte]

end VG.Proof.Weierstrass.AArch64
