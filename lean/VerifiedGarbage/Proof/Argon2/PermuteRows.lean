import VerifiedGarbage.Spec.Argon2

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Spec`. -/
section

/-! # Facts about Argon2's block permutation -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

/-- The four output words of GB in register order. -/
def mix (va vb vc vd : Word) : Word × Word × Word × Word :=
  let a := addMul va vb
  let d := (vd ^^^ a).rotateRight 32
  let c := addMul vc d
  let b := (vb ^^^ c).rotateRight 24
  let a := addMul a b
  let d := (d ^^^ a).rotateRight 16
  let c := addMul c d
  let b := (b ^^^ c).rotateRight 63
  (a, b, c, d)

/-- The register result written to four selected vector positions. -/
def mixWords {n : Nat} (v : Vector Word n) (a b c d : Fin n) : Vector Word n :=
  let x := VG.Proof.Argon2.mix v[a] v[b] v[c] v[d]
  (((v.set a x.1).set b x.2.1).set c x.2.2.1).set d x.2.2.2

/-- Restrict a block to the sixteen words of a row or column. -/
def gather (index : Fin 16 → Fin 128) (v : Block) : Vector Word 16 :=
  Vector.ofFn fun i => v[(index i).val]'(index i).isLt

theorem gather_get (index : Fin 16 → Fin 128) (v : Block) (j : Fin 16) :
    (VG.Proof.Argon2.gather index v)[j] = v[index j] := by
  simp only [VG.Proof.Argon2.gather, Fin.getElem_fin, Vector.getElem_ofFn]

/-- An update through an injective row/column map updates exactly one gathered word. -/
theorem gather_set (index : Fin 16 → Fin 128) (hi : Function.Injective index)
    (v : Block) (a : Fin 16) (x : Word) :
    VG.Proof.Argon2.gather index (v.set (index a) x) = (VG.Proof.Argon2.gather index v).set a x := by
  apply Vector.ext
  intro j hj
  change (VG.Proof.Argon2.gather index (v.set (index a) x))[(⟨j, hj⟩ : Fin 16)] =
    ((VG.Proof.Argon2.gather index v).set a x)[j]
  rw [VG.Proof.Argon2.gather_get]
  simp only [Fin.getElem_fin, Vector.getElem_set]
  have hg : (VG.Proof.Argon2.gather index v)[j] = v[index ⟨j, hj⟩] := VG.Proof.Argon2.gather_get index v ⟨j, hj⟩
  rw [hg]
  have he : (index a).val = (index ⟨j, hj⟩).val ↔ a.val = j := by
    constructor
    · intro h
      exact congrArg Fin.val (hi (Fin.ext h))
    · intro h
      exact congrArg (fun k => (index k).val) (Fin.ext h)
  simp only [he, Fin.getElem_fin]

theorem set_get (v : Vector Word 16) (a : Fin 16) (x : Word) (k : Nat) (hk : k < 16) :
    (v.set a x)[k] = if a.1 = k then x else v[k] := by
  simp [Vector.getElem_set]

theorem set_get_fin (v : Vector Word 16) (a b : Fin 16) (x : Word) :
    (v.set a x)[b] = if a.1 = b.1 then x else v[b] := by
  simp [Vector.getElem_set]

/-- Word `k` after `G` on four distinct words. -/
theorem GB_get (v : Vector Word 16) {a b c d : Fin 16} (hab : a.1 ≠ b.1) (hac : a.1 ≠ c.1)
    (had : a.1 ≠ d.1) (hbc : b.1 ≠ c.1) (hbd : b.1 ≠ d.1) (hcd : c.1 ≠ d.1)
    (k : Nat) (hk : k < 16) :
    (GB v a b c d)[k] =
      if b.1 = k then (VG.Proof.Argon2.mix v[a] v[b] v[c] v[d]).2.1
      else if c.1 = k then (VG.Proof.Argon2.mix v[a] v[b] v[c] v[d]).2.2.1
      else if d.1 = k then (VG.Proof.Argon2.mix v[a] v[b] v[c] v[d]).2.2.2
      else if a.1 = k then (VG.Proof.Argon2.mix v[a] v[b] v[c] v[d]).1 else v[k] := by
  simp only [GB, VG.Proof.Argon2.set_get, VG.Proof.Argon2.set_get_fin, hab, hac, had, hbc, hbd, hcd, Ne.symm hab, Ne.symm hac,
    Ne.symm had, Ne.symm hbc, Ne.symm hbd, Ne.symm hcd, ite_true, ite_false]
  by_cases eb : b.1 = k
  · subst eb; simp only [ite_true, hab, hbc.symm, hbd.symm, ite_false, VG.Proof.Argon2.mix]
  by_cases ec : c.1 = k
  · subst ec; simp only [ite_true, eb, hac, hcd.symm, ite_false, VG.Proof.Argon2.mix]
  by_cases ed : d.1 = k
  · subst ed; simp only [ite_true, eb, ec, had, ite_false, VG.Proof.Argon2.mix]
  by_cases ea : a.1 = k
  · subst ea; simp only [ite_true, eb, ec, ed, ite_false, VG.Proof.Argon2.mix]
  simp only [eb, ec, ed, ea, ite_false]

/-- The four-update form is the RFC's GB on distinct indices. -/
theorem GB_eq_mixWords (v : Vector Word 16) {a b c d : Fin 16}
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
    (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
    GB v a b c d = VG.Proof.Argon2.mixWords v a b c d := by
  apply Vector.ext
  intro j hj
  rw [VG.Proof.Argon2.GB_get v hab hac had hbc hbd hcd j hj]
  simp only [VG.Proof.Argon2.mixWords, Vector.getElem_set]
  by_cases hdj : d.val = j
  · subst j
    simp only [had, hbd, hcd, ite_true, ite_false]
  by_cases hcj : c.val = j
  · subst j
    simp only [hac, hbc, hdj, ite_true, ite_false]
  by_cases hbj : b.val = j
  · subst j
    simp only [hab, hcj, hdj, ite_true, ite_false]
  simp only [hdj, hcj, hbj, ite_false]

theorem gather_mixWords (index : Fin 16 → Fin 128) (hi : Function.Injective index)
    (v : Block) (a b c d : Fin 16) :
    VG.Proof.Argon2.gather index (VG.Proof.Argon2.mixWords v (index a) (index b) (index c) (index d)) =
      VG.Proof.Argon2.mixWords (VG.Proof.Argon2.gather index v) a b c d := by
  unfold VG.Proof.Argon2.mixWords
  rw [VG.Proof.Argon2.gather_set index hi, VG.Proof.Argon2.gather_set index hi, VG.Proof.Argon2.gather_set index hi, VG.Proof.Argon2.gather_set index hi]
  simp only [VG.Proof.Argon2.gather_get]

end VG.Proof.Argon2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Permutation`. -/
section

/-! # Gathering and scattering Argon2 rows and columns -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

/-- Write selected words of a sixteen-word vector back to the block. -/
def scatter (index : Fin 16 → Fin 128) (xs : List (Fin 16))
    (b : Block) (v : Vector Word 16) : Block :=
  xs.foldl (fun b j => b.set (index j) v[j]) b

theorem scatter_preserves (index : Fin 16 → Fin 128) (hi : Function.Injective index)
    (xs : List (Fin 16)) (b : Block) (v : Vector Word 16) (j : Fin 16)
    (h : b[index j] = v[j]) : (VG.Proof.Argon2.scatter index xs b v)[index j] = v[j] := by
  induction xs generalizing b with
  | nil => exact h
  | cons a xs ih =>
    apply ih
    by_cases ha : a = j
    · subst a
      simp only [Fin.getElem_fin, Vector.getElem_set_self]
    · have hn : (index a).val ≠ (index j).val := fun he => ha (hi (Fin.ext he))
      simpa only [Fin.getElem_fin, Vector.getElem_set, hn, ite_false] using h

theorem scatter_at (index : Fin 16 → Fin 128) (hi : Function.Injective index)
    (xs : List (Fin 16)) (b : Block) (v : Vector Word 16) (j : Fin 16)
    (hj : j ∈ xs) : (VG.Proof.Argon2.scatter index xs b v)[index j] = v[j] := by
  induction xs generalizing b with
  | nil => simp only [List.not_mem_nil] at hj
  | cons a xs ih =>
    rcases List.mem_cons.mp hj with h | h
    · subst a
      apply VG.Proof.Argon2.scatter_preserves index hi xs (b.set (index j) v[j])
      simp only [Fin.getElem_fin, Vector.getElem_set_self]
    · exact ih _ h

theorem scatter_outside (index : Fin 16 → Fin 128) (xs : List (Fin 16))
    (b : Block) (v : Vector Word 16) (k : Fin 128)
    (hk : ∀ j ∈ xs, index j ≠ k) : (VG.Proof.Argon2.scatter index xs b v)[k] = b[k] := by
  induction xs generalizing b with
  | nil => rfl
  | cons a xs ih =>
    rw [show VG.Proof.Argon2.scatter index (a :: xs) b v = VG.Proof.Argon2.scatter index xs (b.set (index a) v[a]) v from rfl,
      ih _ (fun j hj => hk j (List.mem_cons_of_mem _ hj))]
    have hn : (index a).val ≠ k.val := fun he => hk a (by simp) (Fin.ext he)
    simp only [Fin.getElem_fin, Vector.getElem_set, hn, ite_false]

/-- A vector matching all selected words and all untouched words is the scatter. -/
theorem eq_scatter (index : Fin 16 → Fin 128) (hi : Function.Injective index)
    (b t : Block) (v : Vector Word 16) (hg : VG.Proof.Argon2.gather index t = v)
    (ho : ∀ k : Fin 128, (∀ j, index j ≠ k) → t[k] = b[k]) :
    t = VG.Proof.Argon2.scatter index (List.finRange 16) b v := by
  apply Vector.ext
  intro k hk
  by_cases h : ∃ j, index j = ⟨k, hk⟩
  · obtain ⟨j, hj⟩ := h
    have he := congrArg (fun x : Vector Word 16 => x[j]) hg
    rw [VG.Proof.Argon2.gather_get] at he
    have hs := VG.Proof.Argon2.scatter_at index hi (List.finRange 16) b v j (List.mem_finRange j)
    simpa only [hj, Fin.getElem_fin] using he.trans hs.symm
  · have hn : ∀ j, index j ≠ ⟨k, hk⟩ := fun j hj => h ⟨j, hj⟩
    exact (ho ⟨k, hk⟩ hn).trans
      (VG.Proof.Argon2.scatter_outside index (List.finRange 16) b v ⟨k, hk⟩ (fun j _ => hn j)).symm

theorem rowIndex_injective (r : Fin 8) : Function.Injective (rowIndex r) := by
  intro a b h
  have := congrArg Fin.val h
  apply Fin.ext
  simp only [rowIndex] at this
  omega

theorem colIndex_injective (c : Fin 8) : Function.Injective (colIndex c) := by
  intro a b h
  have := congrArg Fin.val h
  apply Fin.ext
  simp only [colIndex] at this
  omega

end VG.Proof.Argon2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.PermuteMany`. -/
section

/-!
# P on several rows or columns

Facts about `permuteAt` on a family of disjoint index sets (the rows, or
the columns): P on one set leaves the others alone, so the rows (or
columns) can be permuted in any grouping (`foldl_at`, `foldl_pairs`).
-/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

theorem permuteAt_eq_scatter (index : Fin 16 → Fin 128) (b : Block) :
    permuteAt index b = VG.Proof.Argon2.scatter index (List.finRange 16) b (permute (VG.Proof.Argon2.gather index b)) := rfl

theorem permuteAt_at (index : Fin 16 → Fin 128) (hi : Function.Injective index) (b : Block)
    (j : Fin 16) : (permuteAt index b)[index j] = (permute (VG.Proof.Argon2.gather index b))[j] := by
  rw [VG.Proof.Argon2.permuteAt_eq_scatter]
  exact VG.Proof.Argon2.scatter_at index hi _ b _ j (List.mem_finRange j)

theorem permuteAt_outside (index : Fin 16 → Fin 128) (b : Block) (k : Fin 128)
    (hk : ∀ j, index j ≠ k) : (permuteAt index b)[k] = b[k] := by
  rw [VG.Proof.Argon2.permuteAt_eq_scatter]
  exact VG.Proof.Argon2.scatter_outside index _ b _ k (fun j _ => hk j)

/-- A family of injective index sets, pairwise disjoint. -/
structure Disjoint (index : Fin 8 → Fin 16 → Fin 128) : Prop where
  inj : ∀ a, Function.Injective (index a)
  disj : ∀ a b j j', a ≠ b → index a j ≠ index b j'

theorem rows_disjoint : VG.Proof.Argon2.Disjoint rowIndex :=
  ⟨VG.Proof.Argon2.rowIndex_injective, fun a b j j' h e => h (Fin.ext (by
    have := congrArg Fin.val e
    simp only [rowIndex] at this
    omega))⟩

theorem cols_disjoint : VG.Proof.Argon2.Disjoint colIndex :=
  ⟨VG.Proof.Argon2.colIndex_injective, fun a b j j' h e => h (Fin.ext (by
    have := congrArg Fin.val e
    simp only [colIndex] at this
    omega))⟩

/-- P on set `a` leaves set `r ≠ a` alone. -/
theorem gather_permuteAt {index : Fin 8 → Fin 16 → Fin 128} (hd : VG.Proof.Argon2.Disjoint index) {a r : Fin 8}
    (h : a ≠ r) (b : Block) : VG.Proof.Argon2.gather (index r) (permuteAt (index a) b) = VG.Proof.Argon2.gather (index r) b := by
  apply Vector.ext; intro j hj
  rw [show (VG.Proof.Argon2.gather (index r) (permuteAt (index a) b))[j] =
      (VG.Proof.Argon2.gather (index r) (permuteAt (index a) b))[(⟨j, hj⟩ : Fin 16)] from rfl,
    show (VG.Proof.Argon2.gather (index r) b)[j] = (VG.Proof.Argon2.gather (index r) b)[(⟨j, hj⟩ : Fin 16)] from rfl,
    VG.Proof.Argon2.gather_get, VG.Proof.Argon2.gather_get, VG.Proof.Argon2.permuteAt_outside _ _ _ (fun j' => hd.disj a r j' _ h)]

theorem foldl_outside {index : Fin 8 → Fin 16 → Fin 128} (hd : VG.Proof.Argon2.Disjoint index) {r : Fin 8}
    (L : List (Fin 8)) (hr : r ∉ L) (b : Block) (j : Fin 16) :
    (L.foldl (fun b i => permuteAt (index i) b) b)[index r j] = b[index r j] := by
  induction L generalizing b with
  | nil => rfl
  | cons i L ih =>
    rw [List.foldl_cons, ih (fun h => hr (List.mem_cons_of_mem _ h)),
      VG.Proof.Argon2.permuteAt_outside _ _ _ (fun j' => hd.disj i r j' j (fun e => hr (e ▸ List.mem_cons_self)))]

/-- Set `r`, after P on each set of a list without repeats that contains it. -/
theorem foldl_at {index : Fin 8 → Fin 16 → Fin 128} (hd : VG.Proof.Argon2.Disjoint index) {r : Fin 8}
    (L : List (Fin 8)) (hn : L.Nodup) (hr : r ∈ L) (b : Block) (j : Fin 16) :
    (L.foldl (fun b i => permuteAt (index i) b) b)[index r j] = (permute (VG.Proof.Argon2.gather (index r) b))[j] := by
  induction L generalizing b with
  | nil => simp only [List.not_mem_nil] at hr
  | cons i L ih =>
    rw [List.foldl_cons]
    have hn' := List.nodup_cons.mp hn
    by_cases e : i = r
    · subst e
      rw [VG.Proof.Argon2.foldl_outside hd L hn'.1, VG.Proof.Argon2.permuteAt_at _ (hd.inj i)]
    · rw [ih hn'.2 ((List.mem_cons.mp hr).resolve_left fun h => e h.symm), VG.Proof.Argon2.gather_permuteAt hd e]

/-- The eight sets, in order, as four pairs. -/
theorem foldl_pairs (index : Fin 8 → Fin 16 → Fin 128) (b : Block) :
    (List.finRange 8).foldl (fun b i => permuteAt (index i) b) b =
      (List.range 4).foldl (fun b c => permuteAt (index ⟨(2 * c + 1) % 8, Nat.mod_lt _ (by decide)⟩)
        (permuteAt (index ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩) b)) b := by
  rw [show List.finRange 8 = [0, 1, 2, 3, 4, 5, 6, 7] by decide,
    show List.range 4 = [0, 1, 2, 3] by decide]
  simp only [List.foldl_cons, List.foldl_nil]
  rfl

/-- Word `i` of a block after P on all rows. -/
theorem rows_get (b : Block) (i : Nat) (hi : i < 128) :
    ((List.finRange 8).foldl (fun b r => permuteAt (rowIndex r) b) b)[i] =
      (permute (VG.Proof.Argon2.gather (rowIndex ⟨i / 16, by omega⟩) b))[i % 16]'(by omega) := by
  have := VG.Proof.Argon2.foldl_at VG.Proof.Argon2.rows_disjoint (List.finRange 8) (List.nodup_finRange 8)
    (List.mem_finRange ⟨i / 16, by omega⟩) b ⟨i % 16, by omega⟩
  simpa only [rowIndex, Fin.getElem_fin, show 16 * (i / 16) + i % 16 = i by omega] using this

/-- Word `i` of a block after P on columns `2c` and `2c + 1`. -/
theorem colPair_get {c : Nat} (hc : c < 4) (b : Block) (i : Nat) (hi : i < 128) :
    (permuteAt (colIndex ⟨(2 * c + 1) % 8, Nat.mod_lt _ (by decide)⟩)
      (permuteAt (colIndex ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩) b))[i] =
      if i % 16 / 4 = c then
        (permute (VG.Proof.Argon2.gather (colIndex ⟨i % 16 / 2, by omega⟩) b))[2 * (i / 16) + i % 2]'(by omega)
      else b[i] := by
  have hv : 16 * ((2 * (i / 16) + i % 2) / 2) + 2 * (i % 16 / 2) + (2 * (i / 16) + i % 2) % 2 = i := by
    omega
  by_cases h1 : i % 16 / 2 = 2 * c + 1
  · have ec : (⟨i % 16 / 2, by omega⟩ : Fin 8) = ⟨(2 * c + 1) % 8, Nat.mod_lt _ (by decide)⟩ :=
      Fin.ext (by simp only; omega)
    have := VG.Proof.Argon2.permuteAt_at _ (VG.Proof.Argon2.colIndex_injective ⟨(2 * c + 1) % 8, Nat.mod_lt _ (by decide)⟩)
      (permuteAt (colIndex ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩) b) ⟨2 * (i / 16) + i % 2, by omega⟩
    rw [VG.Proof.Argon2.gather_permuteAt VG.Proof.Argon2.cols_disjoint (fun h => by have := congrArg Fin.val h; simp only at this; omega),
      ← ec] at this
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    simpa only [colIndex, Fin.getElem_fin, ← ec, hv] using this
  · by_cases h0 : i % 16 / 2 = 2 * c
    · have ec : (⟨i % 16 / 2, by omega⟩ : Fin 8) = ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩ :=
        Fin.ext (by simp only; omega)
      have := VG.Proof.Argon2.permuteAt_at _ (VG.Proof.Argon2.colIndex_injective ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩) b
        ⟨2 * (i / 16) + i % 2, by omega⟩
      rw [← VG.Proof.Argon2.permuteAt_outside (colIndex ⟨(2 * c + 1) % 8, Nat.mod_lt _ (by decide)⟩) _ _
        (fun j' => cols_disjoint.disj _ _ j' _
          (fun h => by have := congrArg Fin.val h; simp only at this; omega)), ← ec] at this
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      simpa only [colIndex, Fin.getElem_fin, ← ec, hv] using this
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      have := VG.Proof.Argon2.permuteAt_outside (colIndex ⟨(2 * c + 1) % 8, Nat.mod_lt _ (by decide)⟩)
        (permuteAt (colIndex ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩) b) ⟨i, hi⟩
        (fun j' h => by have := congrArg Fin.val h; simp only [colIndex] at this; omega)
      rw [VG.Proof.Argon2.permuteAt_outside (colIndex ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩) b ⟨i, hi⟩ (fun j' h => by
          have := congrArg Fin.val h; simp only [colIndex] at this; omega)] at this
      simpa only [Fin.getElem_fin] using this

end VG.Proof.Argon2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.PermuteRows`. -/
section

/-!
# P on four columns at once

The sixteen words P permutes, as four rows of four (`4k…4k+3` for
`k < 4`): the four column GBs of P are GB on each column of the rows at once
(`mixColumns`), and the four diagonal GBs are the same after row `k` is
rotated left by `k` places (`rotRows 1`), rotated back after it
(`rotRows 3`). This is how code keeping each row in one vector register
(of four 64-bit lanes) computes P (`permute_lanes`).
-/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

/-- Component `k` of the result of `mix`. -/
def mixAt (k : Nat) (x : Word × Word × Word × Word) : Word :=
  match k with
  | 0 => x.1
  | 1 => x.2.1
  | 2 => x.2.2.1
  | _ => x.2.2.2

/-- GB on each column `q` (words `q`, `4 + q`, `8 + q`, `12 + q`) at once. -/
def mixColumns (v : Vector Word 16) : Vector Word 16 :=
  Vector.ofFn fun j => VG.Proof.Argon2.mixAt (j.val / 4)
    (VG.Proof.Argon2.mix (v[j.val % 4]'(by omega)) (v[4 + j.val % 4]'(by omega)) (v[8 + j.val % 4]'(by omega))
      (v[12 + j.val % 4]'(by omega)))

/-- Row `k` (words `4k…4k+3`) rotated left by `n · k` places. -/
def rotRows (n : Nat) (v : Vector Word 16) : Vector Word 16 :=
  Vector.ofFn fun j => v[4 * (j.val / 4) + (j.val % 4 + n * (j.val / 4)) % 4]'(by omega)

theorem mixColumns_get (v : Vector Word 16) (j : Nat) (hj : j < 16) :
    (VG.Proof.Argon2.mixColumns v)[j] = VG.Proof.Argon2.mixAt (j / 4) (VG.Proof.Argon2.mix (v[j % 4]'(by omega)) (v[4 + j % 4]'(by omega))
      (v[8 + j % 4]'(by omega)) (v[12 + j % 4]'(by omega))) := by
  simp only [VG.Proof.Argon2.mixColumns, Vector.getElem_ofFn]

theorem rotRows_get (n : Nat) (v : Vector Word 16) (j : Nat) (hj : j < 16) :
    (VG.Proof.Argon2.rotRows n v)[j] = v[4 * (j / 4) + (j % 4 + n * (j / 4)) % 4]'(by omega) := by
  simp only [VG.Proof.Argon2.rotRows, Vector.getElem_ofFn]

theorem GB_get' (v : Vector Word 16) {a b c d : Fin 16} (hab : a.1 ≠ b.1) (hac : a.1 ≠ c.1)
    (had : a.1 ≠ d.1) (hbc : b.1 ≠ c.1) (hbd : b.1 ≠ d.1) (hcd : c.1 ≠ d.1)
    (k : Nat) (hk : k < 16) :
    (GB v a b c d)[k] =
      if b.1 = k then (VG.Proof.Argon2.mix v[a.1] v[b.1] v[c.1] v[d.1]).2.1
      else if c.1 = k then (VG.Proof.Argon2.mix v[a.1] v[b.1] v[c.1] v[d.1]).2.2.1
      else if d.1 = k then (VG.Proof.Argon2.mix v[a.1] v[b.1] v[c.1] v[d.1]).2.2.2
      else if a.1 = k then (VG.Proof.Argon2.mix v[a.1] v[b.1] v[c.1] v[d.1]).1 else v[k] :=
  VG.Proof.Argon2.GB_get v hab hac had hbc hbd hcd k hk

theorem cases16 {j : Nat} (hj : j < 16) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨
    j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 := by
  omega

/-- The value of a literal index. -/
theorem val_lit (k : Nat) : (no_index (OfNat.ofNat k : Fin 16)).val = k % 16 := rfl

/-- The four column GBs of P. -/
theorem columns_eq (v : Vector Word 16) :
    GB (GB (GB (GB v 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15 = VG.Proof.Argon2.mixColumns v := by
  apply Vector.ext
  intro j hj
  simp only [VG.Proof.Argon2.mixColumns_get]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl := VG.Proof.Argon2.cases16 hj
  all_goals
    simp (disch := decide) only [VG.Proof.Argon2.GB_get', VG.Proof.Argon2.val_lit, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd,
      Nat.reduceEqDiff, ↓reduceIte, VG.Proof.Argon2.mixAt]

/-- The four diagonal GBs of P. -/
theorem diagonals_eq (v : Vector Word 16) :
    GB (GB (GB (GB v 0 5 10 15) 1 6 11 12) 2 7 8 13) 3 4 9 14 =
      VG.Proof.Argon2.rotRows 3 (VG.Proof.Argon2.mixColumns (VG.Proof.Argon2.rotRows 1 v)) := by
  apply Vector.ext
  intro j hj
  simp only [VG.Proof.Argon2.rotRows_get, VG.Proof.Argon2.mixColumns_get]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl := VG.Proof.Argon2.cases16 hj
  all_goals
    simp (disch := decide) only [VG.Proof.Argon2.GB_get', VG.Proof.Argon2.val_lit, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd,
      Nat.reduceMul, Nat.reduceEqDiff, ↓reduceIte, VG.Proof.Argon2.mixAt]

/-- P is two rounds of GB on the columns of the rows. -/
theorem permute_lanes (v : Vector Word 16) :
    permute v = VG.Proof.Argon2.rotRows 3 (VG.Proof.Argon2.mixColumns (VG.Proof.Argon2.rotRows 1 (VG.Proof.Argon2.mixColumns v))) := by
  rw [← VG.Proof.Argon2.diagonals_eq, ← VG.Proof.Argon2.columns_eq]
  rfl

end VG.Proof.Argon2

end
