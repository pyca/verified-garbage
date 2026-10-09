import VerifiedGarbage.Proof.Weierstrass.Layout

/-!
# The fixed-base comb: where it keeps its numbers

The slots the comb reads and writes, and what it needs of them (`CombLay`):
in the working space and apart (`Lay`), the complete addition writing slots
apart from what it reads, the slots read only not written, and the table of
bits apart from what is written. Facts about offsets, as for the ladder
(`LadLay`).
-/

namespace VG.Proof.Weierstrass

open VG VG.Impl.Mont VG.Impl.Weierstrass VG.Proof.Mont

/-- The slots of the comb. -/
def combSlots (K : CombCfg) : List Nat :=
  [K.S.a, K.S.b3, K.zero, K.A.x, K.A.y, K.A.z, K.E.x, K.E.y, K.E.z, K.neg] ++ rcbW K.S K.D

/-- The slots the comb writes. -/
def combWs (K : CombCfg) : List Nat :=
  [K.A.x, K.A.y, K.A.z, K.E.x, K.E.y, K.E.z, K.neg] ++ rcbW K.S K.D

/-- What the comb writes: its slots and the modulus's temporary area. -/
def combW (K : CombCfg) : List (Nat × Nat) :=
  (combWs K).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)]

/-- The slots it reads only: the curve's `a` and `3b`, and zero. -/
def combRo (K : CombCfg) : List Nat := [K.S.a, K.S.b3, K.zero]

/-- The comb's slots are in the working space and apart (`lay`), the
addition writes slots apart from what it reads (`add`), the slots read only
are not written (`ro`), the slots written are distinct (`nodup`), and the
table of bits (`4 J` bytes) is apart from what is written. -/
structure CombLay (K : CombCfg) (size : Nat) : Prop where
  lay : Lay K.M size (· ∈ combSlots K)
  add : RcbApart K.S K.A K.E K.D
  ro : ∀ x ∈ combRo K, x ∉ combWs K
  nodup : (combWs K).Nodup
  J : 1 ≤ K.J ∧ K.J ≤ 4096
  bits : K.bits + 4 * K.J ≤ size
  bits4 : K.bits + 3 < 4096
  bits_w : ∀ w ∈ combW K, K.bits + 4 * K.J ≤ w.1 ∨ w.1 + w.2 ≤ K.bits

theorem combWs_slots (K : CombCfg) : ∀ x ∈ combWs K, x ∈ combSlots K := by
  intro x hx
  simp only [combWs, combSlots, rcbW, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx ⊢
  grind

/-- A slot the comb does not write is apart from what it writes. -/
theorem CombLay.apart_w {K : CombCfg} {size : Nat} (hL : CombLay K size) {x : Nat}
    (hx : x ∈ combSlots K) (hxw : x ∉ combWs K) :
    ∀ w ∈ combW K, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro w hw
  simp only [combW, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · exact hL.lay.apart x y hx (combWs_slots K y hy) fun h => hxw (h ▸ hy)
  · exact hL.lay.tmp x hx

/-- Two distinct slots the comb writes are apart. -/
theorem CombLay.apart₂ {K : CombCfg} {size : Nat} (hL : CombLay K size) {x y : Nat}
    (hx : x ∈ combWs K) (hy : y ∈ combWs K) (hxy : x ≠ y) :
    x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x :=
  hL.lay.apart x y (combWs_slots K x hx) (combWs_slots K y hy) hxy

/-- `x ∈ l` for the comb's lists. -/
macro "comb_mem" : tactic => `(tactic| first
  | list_mem
  | (simp only [List.mem_cons, List.mem_append, List.mem_singleton, true_or, or_true, combSlots,
      combWs, combRo, rcbW, rcbR, List.cons_append, List.nil_append]))

/-- A slot read only is apart from what the comb writes. -/
theorem combW_ro {K : CombCfg} {size : Nat} (hL : CombLay K size) {x : Nat} (hx : x ∈ combRo K) :
    ∀ w ∈ combW K, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  have hs : x ∈ combSlots K := by
    simp only [combRo, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> comb_mem
  exact hL.apart_w hs (hL.ro x hx)

theorem combRo_slots {K : CombCfg} : ∀ x ∈ combRo K, x ∈ combSlots K := by
  intro x hx
  simp only [combRo, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> comb_mem

end VG.Proof.Weierstrass
