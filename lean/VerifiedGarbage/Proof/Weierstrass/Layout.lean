import VerifiedGarbage.Proof.Weierstrass.Env
import VerifiedGarbage.Proof.Mont.Words

/-!
# Short Weierstrass curves: where the ladder and powers keep their numbers

The slots the ladder reads and writes, and what it needs of them
(`LadLay`): in the working space and apart (`Lay`), the two complete
additions writing slots apart from what they read, and the table of bits
apart from what is written. The same for powers (`PowLay`). These are facts
about offsets, the same on every target.
-/

namespace VG.Proof.Weierstrass

open VG VG.Impl.Mont VG.Impl.Weierstrass VG.Proof.Mont

/-- The slots of the ladder. -/
def ladSlots (L : LadderCfg) : List Nat :=
  [L.S.a, L.S.b3, L.G.x, L.G.y, L.G.z, L.R.x, L.R.y, L.R.z] ++ rcbW L.S L.D ++ [L.T.x, L.T.y, L.T.z]

/-- The slots the ladder writes. -/
def ladWs (L : LadderCfg) : List Nat := [L.R.x, L.R.y, L.R.z] ++ rcbW L.S L.D ++ rcbW L.S L.T

/-- What the ladder writes: its slots and the modulus's temporary area. -/
def ladW (L : LadderCfg) : List (Nat × Nat) :=
  (ladWs L).map (·, 8 * L.M.n) ++ [(L.M.tmp, 8 * L.M.n)]

/-- The slots it reads only: the curve's `a` and `3b`, and `G`. -/
def ladRo (L : LadderCfg) : List Nat := [L.S.a, L.S.b3, L.G.x, L.G.y, L.G.z]

/-- What an iteration reads: those and `R`. -/
def ladR (L : LadderCfg) : List Nat := ladRo L ++ [L.R.x, L.R.y, L.R.z]

/-- The ladder's slots are in the working space and apart (`lay`), the two
additions write slots apart from what they read (`a1`, `a2`), the slots read
only are not written (`ro`), `R`'s are not `D`'s or `T`'s, and the table of
bits is apart from what is written. -/
structure LadLay (L : LadderCfg) (size : Nat) : Prop where
  lay : Lay L.M size (· ∈ ladSlots L)
  a1 : RcbApart L.S L.R L.R L.D
  a2 : RcbApart L.S L.D L.G L.T
  ro : ∀ x ∈ ladRo L, x ∉ ladWs L
  rne : L.R.x ≠ L.R.y ∧ L.R.x ≠ L.R.z ∧ L.R.y ≠ L.R.z
  rdt : ∀ x ∈ [L.R.x, L.R.y, L.R.z], x ∉ [L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z]
  nbits : 1 ≤ L.nbits ∧ L.nbits < 2 ^ 16
  bits : L.bits + L.nbits ≤ size
  bits_w : ∀ w ∈ ladW L, L.bits + L.nbits ≤ w.1 ∨ w.1 + w.2 ≤ L.bits

theorem ladWs_slots (L : LadderCfg) : ∀ x ∈ ladWs L, x ∈ ladSlots L := by
  intro x hx
  simp only [ladWs, ladSlots, rcbW, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx ⊢
  grind

theorem ladR_slots (L : LadderCfg) : ∀ x ∈ ladR L, x ∈ ladSlots L := by
  intro x hx
  simp only [ladR, ladRo, ladSlots, rcbW, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx ⊢
  grind

/-- A slot the ladder does not write is apart from what it writes. -/
theorem LadLay.apart_w {L : LadderCfg} {size : Nat} (hL : LadLay L size) {x : Nat}
    (hx : x ∈ ladSlots L) (hxw : x ∉ ladWs L) :
    ∀ w ∈ ladW L, x + 8 * L.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro w hw
  simp only [ladW, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · exact hL.lay.apart x y hx (ladWs_slots L y hy) fun h => hxw (h ▸ hy)
  · exact hL.lay.tmp x hx

theorem mem_ladRo_ladR {L : LadderCfg} {x : Nat} (h : x ∈ ladRo L) : x ∈ ladR L :=
  List.mem_append_left _ h

/-- `∀ x ∈ l₁, x ∈ l₂` for lists written out. -/
macro "sub_list" : tactic => `(tactic| (show (_ : List Nat) ⊆ _; simp only [List.cons_subset,
  List.nil_subset, List.mem_cons, List.mem_append, List.mem_singleton, true_or, or_true,
  and_true, and_self, ladR, ladRo, ladSlots, ladWs, rcbW, rcbR, List.cons_append, List.nil_append]))

/-- `x ∈ l` for a list written out. -/
macro "mem_list" : tactic => `(tactic| (simp only [List.mem_cons, List.mem_append,
  List.mem_singleton, true_or, or_true, ladR, ladRo, ladSlots, ladWs, rcbW, rcbR, List.cons_append,
  List.nil_append]))

theorem mem_ladW_D {L : LadderCfg} : ∀ w ∈ (rcbW L.S L.D).map (·, 8 * L.M.n) ++ [(L.M.tmp, 8 * L.M.n)],
    w ∈ ladW L := by
  intro w hw
  simp only [ladW, List.mem_append, List.mem_map] at hw ⊢
  rcases hw with ⟨y, hy, rfl⟩ | hw
  · exact Or.inl ⟨y, by simp only [ladWs, List.mem_append]; exact Or.inl (Or.inr hy), rfl⟩
  · exact Or.inr hw

theorem mem_ladW_T {L : LadderCfg} : ∀ w ∈ (rcbW L.S L.T).map (·, 8 * L.M.n) ++ [(L.M.tmp, 8 * L.M.n)],
    w ∈ ladW L := by
  intro w hw
  simp only [ladW, List.mem_append, List.mem_map] at hw ⊢
  rcases hw with ⟨y, hy, rfl⟩ | hw
  · exact Or.inl ⟨y, by simp only [ladWs, List.mem_append]; exact Or.inr hy, rfl⟩
  · exact Or.inr hw

theorem mem_ladW_R {L : LadderCfg} :
    ∀ w ∈ [(L.R.x, 8 * L.M.n), (L.R.y, 8 * L.M.n), (L.R.z, 8 * L.M.n)], w ∈ ladW L := by
  intro w hw
  simp only [ladW, List.mem_append, List.mem_map]
  refine Or.inl ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact ⟨L.R.x, by simp [ladWs], rfl⟩
  · exact ⟨L.R.y, by simp [ladWs], rfl⟩
  · exact ⟨L.R.z, by simp [ladWs], rfl⟩

theorem ladR_V₁ (L : LadderCfg) : ∀ x ∈ rcbR L.S L.R L.R, x ∈ ladR L := by sub_list

theorem ladR_S₁ (L : LadderCfg) : ∀ x ∈ rcbW L.S L.D ++ rcbR L.S L.R L.R, x ∈ ladSlots L := by
  sub_list

theorem ladR_V₂ (L : LadderCfg) : ∀ x ∈ rcbR L.S L.D L.G, x ∈ rcbW L.S L.D ++ ladR L := by sub_list

theorem ladR_S₂ (L : LadderCfg) : ∀ x ∈ rcbW L.S L.T ++ rcbR L.S L.D L.G, x ∈ ladSlots L := by
  sub_list

theorem ladPts_slots (L : LadderCfg) :
    ∀ x ∈ [L.R.x, L.R.y, L.R.z, L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z], x ∈ ladSlots L := by
  sub_list

/-- What a power writes: the accumulator, the temporary and the modulus's
temporary area. -/
def powW (P : PowCfg) : List (Nat × Nat) :=
  [(P.acc, 8 * P.M.n), (P.tmp, 8 * P.M.n), (P.M.tmp, 8 * P.M.n)]

/-- Where a power's slots and table are: in the working space, and what it
reads apart from what it writes. -/
structure PowLay (P : PowCfg) (size : Nat) : Prop where
  acc : P.acc + 8 * P.M.n ≤ size
  tmp : P.tmp + 8 * P.M.n ≤ size
  base : P.base + 8 * P.M.n ≤ size
  one : P.one + 8 * P.M.n ≤ size
  bits : P.bits + P.nbits ≤ size
  nbits : 1 ≤ P.nbits ∧ P.nbits < 2 ^ 16
  acc_tmp : P.acc + 8 * P.M.n ≤ P.tmp ∨ P.tmp + 8 * P.M.n ≤ P.acc
  acc_mtmp : P.acc + 8 * P.M.n ≤ P.M.tmp ∨ P.M.tmp + 8 * P.M.n ≤ P.acc
  acc_one : P.acc + 8 * P.M.n ≤ P.one ∨ P.one + 8 * P.M.n ≤ P.acc
  base_w : ∀ w ∈ powW P, P.base + 8 * P.M.n ≤ w.1 ∨ w.1 + w.2 ≤ P.base
  bits_w : ∀ w ∈ powW P, P.bits + P.nbits ≤ w.1 ∨ w.1 + w.2 ≤ P.bits
  mo_w : ∀ w ∈ powW P, P.M.mo + 8 * P.M.n ≤ w.1 ∨ w.1 + w.2 ≤ P.M.mo

end VG.Proof.Weierstrass
