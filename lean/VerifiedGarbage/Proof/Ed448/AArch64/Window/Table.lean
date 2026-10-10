import VerifiedGarbage.Proof.Ed448.AArch64.Window.Store
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Select
import VerifiedGarbage.Proof.X448.AArch64.Base.AddGen
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Dbl
import VerifiedGarbage.Proof.X448.AArch64.Fast.Weave
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Call

/-!
# Ed448 verification on AArch64: the table of `[n](-A)`

Untrusted: everything here is checked by Lean. The table's 16 entries are
`tabPts P` for the point `P` (`-A`) in slots 6–8: the neutral point, `P`, and
each later entry the one before (in slots 3–5) plus `P`, by a call of
`vg_ed448_r56_point_add` (`tabPts`, with the specification's `addPt`). `TInv` holds after each entry is stored
(`tabBody_ok`), and after the loop for all 16 (`tabLoop_ok`).
-/

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot ACC)
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep Same block_codeOf)
open VG.Impl.X448.AArch64.Fast (codeOf)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (pt genEnv genPt temps addOps_ok zero_env next_ok)
open VG.Spec.Ed448 (Point)
open VG.Proof.X448 (addPt)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E
local notation "FV" => VG.Proof.X448.AArch64.Weak.F

/-! ## The entries -/

/-- Entry `e` of the table, as a point. -/
def TPt (m : Mem) (base : Addr) (e : Nat) : Point :=
  ⟨FV m base (TAB + 192 * e), FV m base (TAB + 192 * e + 64), FV m base (TAB + 192 * e + 128)⟩

/-- Entry `e`'s words below `Ib`. -/
def TBnd (m : Mem) (base : Addr) (e : Nat) : Prop := ∀ w < 24, (tw m base e w).toNat < Ib

/-- The entries from `P`: the neutral point, `P`, and each later one the one before plus `P`. -/
def tabPts (P : Point) : Nat → Point
  | 0 => ⟨0, 1, 1⟩
  | 1 => P
  | e + 2 => addPt (tabPts P (e + 1)) P

theorem tabPts_succ (P : Point) (j : Nat) : tabPts P (j + 2) = addPt (tabPts P (j + 1)) P := rfl

/-- Entries `e < k` are `tabPts P e`, their words below `Ib`. -/
def TabOk (m : Mem) (base : Addr) (P : Point) (k : Nat) : Prop :=
  ∀ e < k, TPt m base e = tabPts P e ∧ TBnd m base e

/-- Coordinate `c` of entry `e` from the words `8c`, …, `8c + 7` of the entry. -/
theorem FV_entry (m m' : Mem) (base : Addr) {e c o : Nat} (ho : o = TAB + 192 * e + 64 * c)
    {o' : Nat} (h : ∀ i < 8, tw m base e (8 * c + i) = word m' base (o' + 8 * i)) :
    FV m base o = FV m' base o' := by
  simp only [VG.Proof.X448.AArch64.Weak.F]
  refine congrArg _ (VG.Proof.X448.Wide.valN_congr fun i hi => ?_)
  simp only [limbs]
  rw [← h i hi, tw]
  congr 2
  omega

/-- After `tabStore` from slots 3–5 of `s`, entry `e` is their point, with their bounds. -/
theorem tabStore_pt {s t : State} {base : Addr} {e : Nat}
    (h : ∀ w < 24, word t.mem base (TAB + 192 * e + 8 * w) = word s.mem base (src w)) :
    TPt t.mem base e = pt (EV s.mem base) 3 4 5 := by
  have hs : ∀ c < 3, ∀ i < 8, tw t.mem base e (8 * c + i) = word s.mem base (slot (3 + c) + 8 * i) :=
    fun c hc i hi => by
      rw [tw, h _ (by omega), src]
      congr 2
      all_goals (try simp only [slot])
      all_goals omega
  simp only [TPt, pt]
  refine Point.mk.injEq _ _ _ _ _ _ |>.mpr ⟨?_, ?_, ?_⟩
  · exact FV_entry _ _ _ (e := e) (c := 0) (o := TAB + 192 * e) (by omega) (hs 0 (by decide))
  · exact FV_entry _ _ _ (e := e) (c := 1) rfl (hs 1 (by decide))
  · exact FV_entry _ _ _ (e := e) (c := 2) rfl (hs 2 (by decide))

theorem tabStore_bnd {s t : State} {base : Addr} {e : Nat} (hb : BEnv s.mem base)
    (h : ∀ w < 24, word t.mem base (TAB + 192 * e + 8 * w) = word s.mem base (src w)) : TBnd t.mem base e := by
  intro w hw
  rw [tw, h w hw]
  have := hb ⟨3 + w / 8, by omega⟩ (w % 8) (Nat.mod_lt _ (by decide))
  exact this

/-- Entries other than `e` are kept by a store to entry `e`. -/
theorem tw_outside {m m' : Mem} {base : Addr} {e : Nat} (h : Outside base (TAB + 192 * e) 192 m m')
    {e' w : Nat} (he : e' ≠ e) (he' : e' < 16) (hw : w < 24) :
    tw m' base e' w = tw m base e' w := by
  unfold tw
  refine h.word ?_ (by simp only [TAB]; omega)
  rcases Nat.lt_or_gt_of_ne he with h1 | h1 <;> [left; right] <;> omega

/-- An entry is its words. -/
theorem TPt_of_tw {m m' : Mem} {base : Addr} {e : Nat} (h : ∀ w < 24, tw m' base e w = tw m base e w) :
    TPt m' base e = TPt m base e := by
  have hc : ∀ c < 3, ∀ i < 8, tw m' base e (8 * c + i) = word m base (TAB + 192 * e + 64 * c + 8 * i) :=
    fun c hc i hi => by
      rw [h _ (by omega)]
      unfold tw
      rw [show TAB + 192 * e + 8 * (8 * c + i) = TAB + 192 * e + 64 * c + 8 * i by omega]
  unfold TPt
  rw [FV_entry m' m base (e := e) (c := 0) (o := TAB + 192 * e) (o' := TAB + 192 * e) (by omega)
      (fun i hi => by rw [hc 0 (by decide) i hi, show TAB + 192 * e + 64 * 0 = TAB + 192 * e by omega]),
    FV_entry m' m base (e := e) (c := 1) (o' := TAB + 192 * e + 64) rfl (fun i hi => hc 1 (by decide) i hi),
    FV_entry m' m base (e := e) (c := 2) (o' := TAB + 192 * e + 128) rfl (fun i hi => hc 2 (by decide) i hi)]

theorem TPt_outside {m m' : Mem} {base : Addr} {e : Nat} (h : Outside base (TAB + 192 * e) 192 m m')
    {e' : Nat} (he : e' ≠ e) (he' : e' < 16) : TPt m' base e' = TPt m base e' :=
  TPt_of_tw fun _ hw => tw_outside h he he' hw

/-! ## The loop -/

/-- What the working space outside the slots, the products' working space and the table
keeps from `s₀`. -/
def TFrame (base : Addr) (m₀ m : Mem) : Prop :=
  ∀ x, (ofs base x < 64 ∨ 2880 ≤ ofs base x) → (ofs base x < ACC ∨ ACC + 1152 ≤ ofs base x) →
    (ofs base x < TAB ∨ TAB + 3072 ≤ ofs base x) → m x = m₀ x

theorem TFrame.trans {base : Addr} {m₁ m₂ m₃ : Mem} (h₁ : TFrame base m₁ m₂) (h₂ : TFrame base m₂ m₃) :
    TFrame base m₁ m₃ := fun x a b c => (h₂ x a b c).trans (h₁ x a b c)

theorem TFrame.of_outside2 {base : Addr} {m m' : Mem} (h : Outside2 base 64 2816 ACC 1152 m m') :
    TFrame base m m' := fun x a b _ => h x a b

theorem TFrame.of_entry {base : Addr} {m m' : Mem} {e : Nat} (he : e < 16)
    (h : Outside base (TAB + 192 * e) 192 m m') : TFrame base m m' := fun x _ _ c =>
  h x (by simp only [TAB] at c ⊢; omega)

/-- The table's loop before entry `k`, from the state `s₀` at its start. -/
structure TInv (s₀ : State) (base : Addr) (P : Point) (k : Nat) (s : State) : Prop where
  bound : 2 ≤ k ∧ k ≤ 16
  scr : Scr s base
  env : BEnv s.mem base
  zero : ∀ w < 8, limbs s.mem base (slot (19 : Index).val) w = 0
  counter : s.gpr .x19 = BitVec.ofNat 64 k
  acc : pt (EV s.mem base) 3 4 5 = tabPts P (k - 1)
  pnt : pt (EV s.mem base) 6 7 8 = P
  one : EV s.mem base 20 = EV s₀.mem base 20
  tab : TabOk s.mem base P k
  chk : s.gpr .x20 = s₀.gpr .x20
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : TFrame base s₀.mem s.mem

theorem tabBody_ok {s₀ s : State} {base : Addr} {P : Point} {k : Nat} (h : TInv s₀ base P k s) (hk : k < 16) :
    WP isa tabBody s fun t => (t.gpr .x9 != 0) = decide (k + 1 ≠ 16) ∧ TInv s₀ base P (k + 1) t := by
  obtain ⟨hb2, hs, hb, hz, hc, hacc, hpnt, hone, htab, hchk, hrd, hwr, hmem⟩ := h
  rw [tabBody, WP.seq_iff]
  refine WP.mono (Point56.addCall_ok hs hb (zero_env hz).2) fun t1 ⟨k1, b1, s1, _, _, _, e1, _⟩ => ?_
  have hs1 := k1.scr hs
  have hc1 : t1.gpr .x19 = BitVec.ofNat 64 k := by rw [k1.regs.1 _ (by decide)]; exact hc
  rw [WP.block_append_iff]
  refine WP.mono (tabStore_ok hs1 hk hc1) fun t2 ⟨w2, o2, k2⟩ => ?_
  have hs2 : Scr t2 base := hs1.of_keeps k2 (by decide)
  have hc2 : t2.gpr .x19 = BitVec.ofNat 64 k := by rw [k2.1 _ (by decide)]; exact hc1
  refine WP.mono (next_ok t2 (n := 16) (by decide) hk hc2) fun t3 ⟨c3, n3, k3, m3⟩ => ⟨n3, ?_⟩
  -- The slots after the addition, and the entries after the store.
  have z1 : ∀ w < 8, limbs t1.mem base (slot (19 : Index).val) w = 0 := fun w hw => by
    rw [s1 19 (by decide) w hw]; exact hz w hw
  have e3 : ∀ i : Index, EV t3.mem base i = EV t1.mem base i := fun i => by
    have := i.isLt
    simp only [VG.Proof.X448.AArch64.Weak.E, VG.Proof.X448.AArch64.Weak.F]
    refine congrArg _ (VG.Proof.X448.Wide.valN_congr fun w hw => ?_)
    rw [m3, o2.limbs (Or.inl (by simp only [slot, TAB]; omega)) (by simp only [slot]; omega) (by omega)]
  have hacc1 : pt (EV t1.mem base) 3 4 5 = tabPts P k := by
    rw [e1, Point56.genEnv_pt, (zero_env hz).1, VG.Proof.X448.AArch64.Base.genPt_eq, hacc, hpnt]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rw [show j + 2 - 1 = j + 1 by omega, tabPts_succ]
  have hpnt1 : pt (EV t1.mem base) 6 7 8 = P := by
    rw [← hpnt]; simp only [pt]
    rw [Same.env s1 (i := 6) (by decide), Same.env s1 (i := 7) (by decide), Same.env s1 (i := 8) (by decide)]
  refine ⟨⟨by omega, by omega⟩, hs2.of_keeps k3 (by decide), ?_, fun w hw => ?_, c3, ?_, ?_, ?_, fun e he => ?_,
    ?_, ?_, ?_, ?_⟩
  · intro i w hw
    have := i.isLt
    show limbs t3.mem base (slot i.val) w < Ib
    rw [m3, o2.limbs (Or.inl (by simp only [slot, TAB]; omega)) (by simp only [slot]; omega) (by omega)]
    exact b1 i w hw
  · rw [m3, o2.limbs (Or.inl (by simp only [slot, TAB]; omega)) (by simp only [slot]; omega) (by omega)]
    exact z1 w hw
  · simp only [pt]; rw [e3 3, e3 4, e3 5, Nat.add_sub_cancel]; exact hacc1
  · simp only [pt]; rw [e3 6, e3 7, e3 8]; exact hpnt1
  · rw [e3 20, ← hone]; exact Same.env s1 (i := 20) (by decide)
  · rw [m3]
    by_cases hek : e = k
    · subst hek
      exact ⟨by rw [tabStore_pt w2, hacc1], tabStore_bnd b1 w2⟩
    · have ⟨te, tb⟩ := htab e (by omega)
      have hmem1 : ∀ w < 24, tw t1.mem base e w = tw s.mem base e w := fun w hw => by
        unfold tw
        exact k1.mem.word (Or.inr (by simp only [TAB]; omega)) (Or.inr (by simp only [ACC, TAB]; omega))
          (by simp only [TAB]; omega)
      refine ⟨?_, fun w hw => ?_⟩
      · rw [TPt_outside o2 hek (by omega), TPt_of_tw hmem1, te]
      · rw [tw_outside o2 hek (by omega) hw, hmem1 w hw]; exact tb w hw
  · rw [k3.1 _ (by decide), k2.1 _ (by decide), k1.regs.1 _ (by decide)]; exact hchk
  · rw [k3.2.1, k2.2.1, k1.regs.2.1]; exact hrd
  · rw [k3.2.2, k2.2.2, k1.regs.2.2]; exact hwr
  · rw [m3]
    exact hmem.trans ((TFrame.of_outside2 k1.mem).trans (TFrame.of_entry hk o2))

theorem tabLoop_ok {s₀ : State} {base : Addr} {P : Point} :
    ∀ m, ∀ s, 1 ≤ m → m ≤ 14 → TInv s₀ base P (16 - m) s →
      WP isa (.loop tabBody (.nonzero .x .x9)) s fun t => TInv s₀ base P 16 t := by
  intro m s h1 h2 hi
  refine WP.loop (M := isa) (body := tabBody) (c := .nonzero .x .x9)
    (Q := fun t => TInv s₀ base P 16 t)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 14 ∧ TInv s₀ base P (16 - m) s) ?_ m s ⟨h1, h2, hi⟩
  intro m s ⟨h1, h2, hi⟩
  refine WP.mono (tabBody_ok hi (by omega)) fun t ⟨hz, ht⟩ => ?_
  simp only [eval, State.read, BitVec.setWidth_eq, hz]
  by_cases hm : m = 1
  · subst hm
    exact .inl ⟨by decide, ht⟩
  · refine .inr ⟨congrArg some (decide_eq_true (by omega)), m - 1, by omega, by omega, by omega, ?_⟩
    rw [show 16 - (m - 1) = 16 - m + 1 by omega]
    exact ht

end VG.Proof.Ed448.AArch64.Window
