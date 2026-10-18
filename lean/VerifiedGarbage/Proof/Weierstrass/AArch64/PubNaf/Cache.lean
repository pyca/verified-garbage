module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.State
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-!
# The public NAF's cache of the entries' `Z²` and `Z³`

After the table, each entry's `Z²` and `Z³` are kept above every slot of the
window method (`cacheAt`, `CacheLay`), in `cacheW`: `CacheOk` says they are
the squares and cubes of the entries' `z`, below `p`; what the loop writes
(`loopW`) keeps them (`CacheOk.unch`). The multiplication's facts about the
state before it (`NafFixed`) hold of the state after the cache
(`NafFixed.rebase`), from which the loop goes on.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.PubNaf

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

theorem cacheAt_eq (K : WinCfg) (a : Nat) :
    cacheAt K a = cacheAt K 1 + 16 * K.M.n * (a - 1) := by
  simp only [cacheAt, Nat.sub_self, Nat.mul_zero, Nat.add_zero]

/-- Entry `a`'s cached `Z²` and `Z³` are its `z`'s square and cube, below `p`. -/
def CacheEntry (K : WinCfg) (C : Curve) (base : Addr) (s : State) (a : Nat) : Prop :=
  wordsVal s.mem base (cacheAt K a) K.M.n < C.p ∧
  wordsVal s.mem base (cacheAt K a + 8 * K.M.n) K.M.n < C.p ∧
  tmv C K.M.n base s (cacheAt K a) =
    tmv C K.M.n base s (K.tblPt a).z * tmv C K.M.n base s (K.tblPt a).z ∧
  tmv C K.M.n base s (cacheAt K a + 8 * K.M.n) =
    tmv C K.M.n base s (K.tblPt a).z *
      (tmv C K.M.n base s (K.tblPt a).z * tmv C K.M.n base s (K.tblPt a).z)

/-- Entries `1 … m` are cached. -/
def CacheUpTo (K : WinCfg) (C : Curve) (base : Addr) (m : Nat) (s : State) : Prop :=
  ∀ a, 1 ≤ a → a ≤ m → CacheEntry K C base s a

/-- The eight entries are cached. -/
abbrev CacheOk (K : WinCfg) (C : Curve) (base : Addr) (s : State) : Prop := CacheUpTo K C base 8 s

/-- What the loop writes is below the cache. -/
theorem CacheLay.loopW {K : WinCfg} {size : Nat} (hC : CacheLay K size) :
    ∀ w ∈ loopW K, w.1 + w.2 ≤ cacheAt K 1 := by
  intro w hw
  simp only [VG.Proof.Weierstrass.AArch64.loopW, List.mem_append, List.mem_map,
    List.mem_singleton] at hw
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · exact hC.slots y (winOther_mem hy)
  · exact hC.tmp

/-- What the window method writes is below the cache. -/
theorem CacheLay.winW {K : WinCfg} {size : Nat} (hC : CacheLay K size) :
    ∀ w ∈ winW K, w.1 + w.2 ≤ cacheAt K 1 := by
  intro w hw
  simp only [VG.Proof.Weierstrass.winW, winWs, List.mem_append, List.mem_map,
    List.mem_singleton] at hw
  rcases hw with ⟨y, hy | hy, rfl⟩ | rfl
  · exact hC.slots y (winOther_mem hy)
  · exact hC.slots y (by simp only [winSlots, List.mem_append]; exact Or.inr hy)
  · exact hC.tmp

/-- Ranges apart from the table and the cache of entries `1 … m`: below the
cache and apart from the table, or above entry `m`'s cache. -/
def Away (K : WinCfg) (m : Nat) (W : List (Nat × Nat)) : Prop :=
  ∀ w ∈ W, (w.1 + w.2 ≤ cacheAt K 1 ∧ ∀ i < 24, K.tbl + 8 * K.M.n * i + 8 * K.M.n ≤ w.1 ∨
    w.1 + w.2 ≤ K.tbl + 8 * K.M.n * i) ∨ cacheAt K (m + 1) ≤ w.1

theorem away_loopW {K : WinCfg} {size : Nat} (hL : WinLay K size) (hC : CacheLay K size) (m : Nat) :
    Away K m (loopW K) := by
  intro w hw
  refine Or.inl ⟨hC.loopW w hw, fun i hi => ?_⟩
  simp only [VG.Proof.Weierstrass.AArch64.loopW, List.mem_append, List.mem_map,
    List.mem_singleton] at hw
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · rcases hL.tbl_apart (List.mem_append_right _ hy) hi with h | h
    · exact Or.inr h
    · exact Or.inl h
  · have hs : K.tbl + 8 * K.M.n * i ∈ winSlots K := by
      simp only [winSlots, List.mem_append]; exact Or.inr (winTbl_mem K hi)
    rcases hL.lay.tmp _ hs with h | h
    · exact Or.inl h
    · exact Or.inr h

theorem away_append {K : WinCfg} {m : Nat} {W W' : List (Nat × Nat)} (h : Away K m W)
    (h' : Away K m W') : Away K m (W ++ W') := fun w hw =>
  (List.mem_append.mp hw).elim (h w) (h' w)

/-- The cached entries survive changes away from them and from the table. -/
theorem CacheUpTo.unch {K : WinCfg} {C : Curve} {base : Addr} {size m : Nat} (hL : WinLay K size)
    (hC : CacheLay K size) (hm : m ≤ 8) {s s' : State} (h : CacheUpTo K C base m s)
    {W : List (Nat × Nat)} (hU : Unch base W s.mem s'.mem) (hW : Away K m W)
    (hn : base.toNat + size ≤ 2 ^ 64) : CacheUpTo K C base m s' := by
  intro a h1 h8
  obtain ⟨l2, l3, e2, e3⟩ := h a h1 h8
  have hc : ∀ c ≤ 8 * K.M.n, wordsVal s'.mem base (cacheAt K a + c) K.M.n =
      wordsVal s.mem base (cacheAt K a + c) K.M.n := fun c hc => by
    have hm8 := Nat.mul_le_mul_left (16 * K.M.n) (show a - 1 + 1 ≤ 8 by omega)
    have hma := Nat.mul_le_mul_left (16 * K.M.n) (show a ≤ m by omega)
    rw [Nat.mul_add, Nat.mul_one] at hm8
    have ht := hC.top
    refine hU.wordsVal (fun w hw => ?_) (by rw [cacheAt_eq K a]; omega)
    rcases hW w hw with ⟨hw1, -⟩ | hw1
    · right; rw [cacheAt_eq K a]; omega
    · left; rw [cacheAt_eq K (m + 1)] at hw1; rw [cacheAt_eq K a]
      have : 16 * K.M.n * (a - 1) + 16 * K.M.n ≤ 16 * K.M.n * (m + 1 - 1) := by
        rw [Nat.add_sub_cancel]; have := Nat.mul_le_mul_left (16 * K.M.n) (show a - 1 + 1 ≤ m by omega)
        rw [Nat.mul_add, Nat.mul_one] at this; exact this
      omega
  have c0 := hc 0 (Nat.zero_le _)
  have c8 := hc (8 * K.M.n) (Nat.le_refl _)
  rw [Nat.add_zero] at c0
  obtain ⟨i, hi, ez, -, -⟩ := tblPt_mem K h1 (by omega) (K.tblPt a).z (by simp)
  have hs : (K.tblPt a).z ∈ winSlots K := by
    rw [ez]; simp only [winSlots, List.mem_append]; exact Or.inr (winTbl_mem K hi)
  have ez' : wordsVal s'.mem base (K.tblPt a).z K.M.n = wordsVal s.mem base (K.tblPt a).z K.M.n := by
    refine hU.wordsVal (fun w hw => ?_) (by have := hL.lay.le _ hs; omega_using [hn, this])
    rw [ez]
    rcases hW w hw with ⟨-, ht⟩ | hw1
    · rcases ht i hi with h | h
      · exact Or.inl h
      · exact Or.inr h
    · left
      have := hC.slots _ hs
      rw [ez] at this
      have : cacheAt K 1 ≤ cacheAt K (m + 1) := by rw [cacheAt_eq K (m + 1)]; omega
      omega
  have tz : tmv C K.M.n base s' (K.tblPt a).z = tmv C K.M.n base s (K.tblPt a).z := by
    show toM _ _ _ = toM _ _ _; rw [ez']
  have t0 : tmv C K.M.n base s' (cacheAt K a) = tmv C K.M.n base s (cacheAt K a) := by
    show toM _ _ _ = toM _ _ _; rw [c0]
  have t8 : tmv C K.M.n base s' (cacheAt K a + 8 * K.M.n) =
      tmv C K.M.n base s (cacheAt K a + 8 * K.M.n) := by
    show toM _ _ _ = toM _ _ _; rw [c8]
  exact ⟨c0 ▸ l2, c8 ▸ l3, by rw [t0, tz]; exact e2, by rw [t8, tz]; exact e3⟩

/-- The cache survives what the loop writes. -/
theorem CacheOk.unch {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hC : CacheLay K size) {s s' : State} (h : CacheOk K C base s)
    (hU : Unch base (loopW K) s.mem s'.mem) (hn : base.toNat + size ≤ 2 ^ 64) :
    CacheOk K C base s' :=
  CacheUpTo.unch hL hC (Nat.le_refl _) h hU (away_loopW hL hC 8) hn

/-- The cache depends on memory alone. -/
theorem CacheUpTo.ofMem {K : WinCfg} {C : Curve} {base : Addr} {m : Nat} {s t : State}
    (hm : t.mem = s.mem) (h : CacheUpTo K C base m s) : CacheUpTo K C base m t := by
  intro a h1 h8
  have e : ∀ x, tmv C K.M.n base t x = tmv C K.M.n base s x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [hm]
  obtain ⟨l2, l3, e2, e3⟩ := h a h1 h8
  refine ⟨hm ▸ l2, hm ▸ l3, ?_, ?_⟩ <;> simp only [e]
  exacts [e2, e3]

/-- The facts about the state before the multiplication hold after the table
and the cache, which write the window method's slots and the cache. -/
theorem NafFixed.rebase {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    {P : Point C} {s₀ s : State} (hF : NafFixed K C base s₀ P k)
    (hU : Unch base (winW K ++ cacheW K) s₀.mem s.mem) (hn : base.toNat + size ≤ 2 ^ 64) :
    NafFixed K C base s P k := by
  have hW := hL.win
  have hC := hL.cache
  have ro : ∀ x ∈ winRo K, wordsVal s.mem base x K.M.n = wordsVal s₀.mem base x K.M.n := by
    intro x hx
    have hs := winRo_slots K x hx
    refine hU.wordsVal (fun w hw => ?_) (by have := hW.lay.le x hs; omega_using [hn, this])
    rcases List.mem_append.mp hw with hw | hw
    · exact hW.ro_w hx w hw
    · simp only [cacheW, List.mem_singleton] at hw
      subst hw
      exact Or.inl (hC.slots x hs)
  have hz : K.zero ∈ winRo K := by simp [winRo]
  have hPx : K.P.x ∈ winRo K := by simp [winRo]
  have hPy : K.P.y ∈ winRo K := by simp [winRo]
  have hPz : K.P.z ∈ winRo K := by simp [winRo]
  have tm : ∀ x ∈ winRo K, tmv C K.M.n base s x = tmv C K.M.n base s₀ x := fun x hx => by
    show toM _ _ _ = toM _ _ _; rw [ro x hx]
  refine ⟨fun x hx => by rw [ro x hx]; exact hF.ro_lt x hx, by rw [ro _ hz]; exact hF.zero,
    by rw [tm _ hPx, tm _ hPy, tm _ hPz]; exact hF.pt, fun t ht => ?_⟩
  have hb := hW.bits
  have hd := hL.digits
  rw [hU.byte (fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · have := hW.bits_w w hw; omega
    · simp only [cacheW, List.mem_singleton] at hw
      subst hw
      have := hC.bits; exact Or.inl (by simp only; omega)) (by omega)]
  exact hF.digits t ht

end VG.Proof.Weierstrass.AArch64.PubNaf
