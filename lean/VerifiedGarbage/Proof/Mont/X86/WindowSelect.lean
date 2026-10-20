module

import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Impl.Mont.X86.Window
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Reading the window's table entry by a masked scan of the whole table -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont
open VG.Proof.Mont.X86

theorem window_mask_small : ∀ a < 16, ∀ j < 16,
    0 - ((BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 j) - 1) >>> 31 =
      if a = j then BitVec.allOnes 32 else 0 := by
  decide

theorem window_mask (x : BitVec 32) (hx : x.toNat < 16) {j : Nat} (hj : j < 16) :
    0 - ((x ^^^ BitVec.ofNat 32 j) - 1) >>> 31 = if x.toNat = j then BitVec.allOnes 32 else 0 := by
  have e : x = BitVec.ofNat 32 x.toNat :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt])
  rw [e, window_mask_small _ hx _ hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- ECX all ones exactly when the window word is `j`. -/
theorem windowMask_ok {s : State} {base : Addr} {size j : Nat} (hs : Scr s base size)
    (hsz : 8 ≤ size) (hw : w32 s.mem base 4 < 16) (hj : j < 16) :
    WP isa (.block (VG.Impl.Mont.X86.Dynamic.windowMask j)) s fun t =>
      t.mem = s.mem ∧
      t.gpr .ecx = (if w32 s.mem base 4 = j then BitVec.allOnes 32 else 0) ∧
      Keeps [.eax, .ecx] s t := by
  unfold VG.Impl.Mont.X86.Dynamic.windowMask VG.Impl.Mont.X86.Dynamic.windowOffset
  refine wp_movS (readSrc_sc hs (d := 4) (by omega)) fun s₁ u₁ _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₂ u₂ => ?_
  refine wp_subS rfl fun s₃ u₃ _ => ?_
  refine wp_shr (by decide) fun s₄ u₄ _ => ?_
  refine wp_movS rfl fun s₅ u₅ _ => ?_
  refine wp_subS rfl fun t u₆ _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
    simp only [reduceCtorEq, ↓reduceIte]
    exact window_mask _ hw hj
  · exact (((((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps).widen u₄.keeps).widen
      u₅.keeps).widen u₆.keeps

/-- Copy `n` 64-bit words. -/
theorem copyWords_ok {s : State} {base : Addr} {bytes n src dst : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hsrc : src + 8 * n ≤ bytes) (hdst : dst + 8 * n ≤ bytes)
    (apart : dst = src ∨ dst + 8 * n ≤ src ∨ src + 8 * n ≤ dst) :
    WP isa (VG.Impl.Mont.X86.Dynamic.copyWords n src dst) s fun t =>
      wordsVal t.mem base dst n = wordsVal s.mem base src n ∧
      Outside base dst (8 * n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  unfold VG.Impl.Mont.X86.Dynamic.copyWords
  refine WP.seq (wp_movS rfl fun u U _ => WP.block_nil ?_)
  refine WP.mono (selectsW_ok (hs.of_keeps U.keeps (by decide)) false U.gpr (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)) fun t ⟨O, V, K⟩ => ?_
  refine ⟨?_, ?_, (U.keeps.mono (by decide)).trans (K.mono (by decide))⟩
  · rw [wordsVal_eq_val32, wordsVal_eq_val32, V, U.mem]
    simp only [ite_self]
  · rw [U.mem] at O
    simpa only [show 4 * (2 * n) = 8 * n by omega] using O

/-- The table of 16 entries of `n` words at `tab`, `dst` apart from it and
from the window word, all in the working space. -/
structure TableLay (n tab dst size : Nat) : Prop where
  n0 : 0 < n
  tab_le : tab + 128 * n ≤ size
  dst_le : dst + 8 * n ≤ size
  apart : dst + 8 * n ≤ tab ∨ tab + 128 * n ≤ dst
  tab8 : 8 ≤ tab
  dst8 : 8 ≤ dst

theorem TableLay.entry {n tab dst size j : Nat} (L : TableLay n tab dst size) (hj : j < 16) :
    VG.Impl.Mont.X86.Dynamic.entry n tab j + 8 * n ≤ size ∧
    (dst + 8 * n ≤ VG.Impl.Mont.X86.Dynamic.entry n tab j ∨
      VG.Impl.Mont.X86.Dynamic.entry n tab j + 8 * n ≤ dst) ∧
    tab ≤ VG.Impl.Mont.X86.Dynamic.entry n tab j ∧
    VG.Impl.Mont.X86.Dynamic.entry n tab j + 8 * n ≤ tab + 128 * n := by
  have := L.tab_le
  have := L.apart
  have h1 : 8 * n * j + 8 * n ≤ 128 * n := by
    have := Nat.mul_le_mul_left (8 * n) (show j + 1 ≤ 16 by omega)
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  unfold VG.Impl.Mont.X86.Dynamic.entry
  omega

/-- The entries `1` to `k` over `dst`, each where the window names it. -/
theorem selectEntries_ok {s : State} {base : Addr} {size n tab dst : Nat}
    (hs : Scr s base size) (L : TableLay n tab dst size) (hw : w32 s.mem base 4 < 16) :
    ∀ k, k < 16 →
    WP isa (VG.Impl.Mont.X86.Dynamic.selectEntries n tab dst k) s fun t =>
      Outside base dst (8 * n) s.mem t.mem ∧
      wordsVal t.mem base dst n =
        (if 0 < w32 s.mem base 4 ∧ w32 s.mem base 4 ≤ k then
          wordsVal s.mem base (VG.Impl.Mont.X86.Dynamic.entry n tab (w32 s.mem base 4)) n
        else wordsVal s.mem base dst n) ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _,
      (ite_eq_right_iff.mpr fun h => absurd h (by omega)).symm, Keeps.refl _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    have d8 := L.dst8
    have ld := L.dst_le
    refine WP.seq (WP.mono (selectEntries_ok hs L hw k (by omega)) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have hs₁ := hs.of_keeps K₁ (by decide)
    have win : w32 s₁.mem base 4 = w32 s.mem base 4 := O₁.w32 (by omega) (by omega)
    refine WP.seq (WP.mono (windowMask_ok hs₁ (by omega) (win ▸ hw) hk) fun s₂ ⟨M₂, C₂, K₂⟩ => ?_)
    have hs₂ := hs₁.of_keeps K₂ (by decide)
    obtain ⟨eb, esep, etab, etop⟩ := L.entry (j := k + 1) hk
    refine WP.mono (selectsW_ok hs₂ (decide (w32 s.mem base 4 = k + 1))
      (by rw [C₂, win]; simp only [decide_eq_true_eq]) (by have := L.n0; omega)
      (by omega) (by omega) (by omega) (.inl rfl) (by omega)) fun t ⟨O₃, V₃, K₃⟩ => ?_
    rw [M₂, show 4 * (2 * n) = 8 * n by omega] at O₃
    rw [M₂] at V₃
    refine ⟨O₁.trans O₃, ?_, (K₁.trans (K₂.mono (by decide))).trans (K₃.mono (by decide))⟩
    have entry_keep (j : Nat) (hj : j < 16) :
        wordsVal s₁.mem base (VG.Impl.Mont.X86.Dynamic.entry n tab j) n =
          wordsVal s.mem base (VG.Impl.Mont.X86.Dynamic.entry n tab j) n := by
      obtain ⟨eb', esep', _, _⟩ := L.entry (j := j) hj
      exact O₁.wordsVal esep'.symm (by omega)
    rw [wordsVal_eq_val32, V₃]
    by_cases hj : w32 s.mem base 4 = k + 1
    · simp only [hj, decide_true, ite_true, Nat.le_refl, and_self, Nat.zero_lt_succ]
      rw [← wordsVal_eq_val32, entry_keep _ hk]
    · simp only [hj, decide_false, Bool.false_eq_true, ite_false]
      rw [← wordsVal_eq_val32, V₁]
      have e : (0 < w32 s.mem base 4 ∧ w32 s.mem base 4 ≤ k + 1) ↔ (0 < w32 s.mem base 4 ∧ w32 s.mem base 4 ≤ k) := by
        omega
      simp only [e]

/-- The window's entry into `dst`. -/
theorem selectWindow_ok {s : State} {base : Addr} {size n tab dst : Nat}
    (hs : Scr s base size) (L : TableLay n tab dst size) (hw : w32 s.mem base 4 < 16) :
    WP isa (VG.Impl.Mont.X86.Dynamic.selectWindow n tab dst) s fun t =>
      Outside base dst (8 * n) s.mem t.mem ∧
      wordsVal t.mem base dst n =
        wordsVal s.mem base (VG.Impl.Mont.X86.Dynamic.entry n tab (w32 s.mem base 4)) n ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have hn := hs.nowrap
  have d8 := L.dst8
  have ld := L.dst_le
  obtain ⟨eb, esep, _, _⟩ := L.entry (j := 0) (by decide)
  unfold VG.Impl.Mont.X86.Dynamic.selectWindow
  refine WP.seq (WP.mono (copyWords_ok hs L.n0 eb ld (.inr esep)) fun s₁ ⟨V₁, O₁, K₁⟩ => ?_)
  have hs₁ := hs.of_keeps K₁ (by decide)
  have win : w32 s₁.mem base 4 = w32 s.mem base 4 := O₁.w32 (by omega) (by omega)
  refine WP.mono (selectEntries_ok hs₁ L (win ▸ hw) 15 (by decide)) fun t ⟨O₂, V₂, K₂⟩ => ?_
  refine ⟨O₁.trans O₂, ?_, K₁.trans K₂⟩
  rw [V₂, win]
  have entry_keep (j : Nat) (hj : j < 16) :
      wordsVal s₁.mem base (VG.Impl.Mont.X86.Dynamic.entry n tab j) n =
        wordsVal s.mem base (VG.Impl.Mont.X86.Dynamic.entry n tab j) n := by
    obtain ⟨eb', esep', _, _⟩ := L.entry (j := j) hj
    exact O₁.wordsVal esep'.symm (by omega)
  split
  · exact entry_keep _ hw
  · rw [V₁]
    have : w32 s.mem base 4 = 0 := by omega
    rw [this]

end VG.Proof.Mont.X86.Dynamic
