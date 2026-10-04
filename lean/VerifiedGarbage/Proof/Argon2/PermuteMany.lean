import VerifiedGarbage.Proof.Argon2.Permutation

/-!
# P on several rows or columns

Facts about `permuteAt` on a family of disjoint index sets (the rows, or
the columns): P on one set leaves the others alone, so the rows (or
columns) can be permuted in any grouping (`foldl_at`, `foldl_pairs`).
-/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

theorem permuteAt_eq_scatter (index : Fin 16 → Fin 128) (b : Block) :
    permuteAt index b = scatter index (List.finRange 16) b (permute (gather index b)) := rfl

theorem permuteAt_at (index : Fin 16 → Fin 128) (hi : Function.Injective index) (b : Block)
    (j : Fin 16) : (permuteAt index b)[index j] = (permute (gather index b))[j] := by
  rw [permuteAt_eq_scatter]
  exact scatter_at index hi _ b _ j (List.mem_finRange j)

theorem permuteAt_outside (index : Fin 16 → Fin 128) (b : Block) (k : Fin 128)
    (hk : ∀ j, index j ≠ k) : (permuteAt index b)[k] = b[k] := by
  rw [permuteAt_eq_scatter]
  exact scatter_outside index _ b _ k (fun j _ => hk j)

/-- A family of injective index sets, pairwise disjoint. -/
structure Disjoint (index : Fin 8 → Fin 16 → Fin 128) : Prop where
  inj : ∀ a, Function.Injective (index a)
  disj : ∀ a b j j', a ≠ b → index a j ≠ index b j'

theorem rows_disjoint : Disjoint rowIndex :=
  ⟨rowIndex_injective, fun a b j j' h e => h (Fin.ext (by
    have := congrArg Fin.val e
    simp only [rowIndex] at this
    omega))⟩

theorem cols_disjoint : Disjoint colIndex :=
  ⟨colIndex_injective, fun a b j j' h e => h (Fin.ext (by
    have := congrArg Fin.val e
    simp only [colIndex] at this
    omega))⟩

/-- P on set `a` leaves set `r ≠ a` alone. -/
theorem gather_permuteAt {index : Fin 8 → Fin 16 → Fin 128} (hd : Disjoint index) {a r : Fin 8}
    (h : a ≠ r) (b : Block) : gather (index r) (permuteAt (index a) b) = gather (index r) b := by
  apply Vector.ext; intro j hj
  rw [show (gather (index r) (permuteAt (index a) b))[j] =
      (gather (index r) (permuteAt (index a) b))[(⟨j, hj⟩ : Fin 16)] from rfl,
    show (gather (index r) b)[j] = (gather (index r) b)[(⟨j, hj⟩ : Fin 16)] from rfl,
    gather_get, gather_get, permuteAt_outside _ _ _ (fun j' => hd.disj a r j' _ h)]

theorem foldl_outside {index : Fin 8 → Fin 16 → Fin 128} (hd : Disjoint index) {r : Fin 8}
    (L : List (Fin 8)) (hr : r ∉ L) (b : Block) (j : Fin 16) :
    (L.foldl (fun b i => permuteAt (index i) b) b)[index r j] = b[index r j] := by
  induction L generalizing b with
  | nil => rfl
  | cons i L ih =>
    rw [List.foldl_cons, ih (fun h => hr (List.mem_cons_of_mem _ h)),
      permuteAt_outside _ _ _ (fun j' => hd.disj i r j' j (fun e => hr (e ▸ List.mem_cons_self)))]

/-- Set `r`, after P on each set of a list without repeats that contains it. -/
theorem foldl_at {index : Fin 8 → Fin 16 → Fin 128} (hd : Disjoint index) {r : Fin 8}
    (L : List (Fin 8)) (hn : L.Nodup) (hr : r ∈ L) (b : Block) (j : Fin 16) :
    (L.foldl (fun b i => permuteAt (index i) b) b)[index r j] = (permute (gather (index r) b))[j] := by
  induction L generalizing b with
  | nil => simp only [List.not_mem_nil] at hr
  | cons i L ih =>
    rw [List.foldl_cons]
    have hn' := List.nodup_cons.mp hn
    by_cases e : i = r
    · subst e
      rw [foldl_outside hd L hn'.1, permuteAt_at _ (hd.inj i)]
    · rw [ih hn'.2 ((List.mem_cons.mp hr).resolve_left fun h => e h.symm), gather_permuteAt hd e]

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
      (permute (gather (rowIndex ⟨i / 16, by omega⟩) b))[i % 16]'(by omega) := by
  have := foldl_at rows_disjoint (List.finRange 8) (List.nodup_finRange 8)
    (List.mem_finRange ⟨i / 16, by omega⟩) b ⟨i % 16, by omega⟩
  simpa only [rowIndex, Fin.getElem_fin, show 16 * (i / 16) + i % 16 = i by omega] using this

/-- Word `i` of a block after P on columns `2c` and `2c + 1`. -/
theorem colPair_get {c : Nat} (hc : c < 4) (b : Block) (i : Nat) (hi : i < 128) :
    (permuteAt (colIndex ⟨(2 * c + 1) % 8, Nat.mod_lt _ (by decide)⟩)
      (permuteAt (colIndex ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩) b))[i] =
      if i % 16 / 4 = c then
        (permute (gather (colIndex ⟨i % 16 / 2, by omega⟩) b))[2 * (i / 16) + i % 2]'(by omega)
      else b[i] := by
  have hv : 16 * ((2 * (i / 16) + i % 2) / 2) + 2 * (i % 16 / 2) + (2 * (i / 16) + i % 2) % 2 = i := by
    omega
  by_cases h1 : i % 16 / 2 = 2 * c + 1
  · have ec : (⟨i % 16 / 2, by omega⟩ : Fin 8) = ⟨(2 * c + 1) % 8, Nat.mod_lt _ (by decide)⟩ :=
      Fin.ext (by simp only; omega)
    have := permuteAt_at _ (colIndex_injective ⟨(2 * c + 1) % 8, Nat.mod_lt _ (by decide)⟩)
      (permuteAt (colIndex ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩) b) ⟨2 * (i / 16) + i % 2, by omega⟩
    rw [gather_permuteAt cols_disjoint (fun h => by have := congrArg Fin.val h; simp only at this; omega),
      ← ec] at this
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    simpa only [colIndex, Fin.getElem_fin, ← ec, hv] using this
  · by_cases h0 : i % 16 / 2 = 2 * c
    · have ec : (⟨i % 16 / 2, by omega⟩ : Fin 8) = ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩ :=
        Fin.ext (by simp only; omega)
      have := permuteAt_at _ (colIndex_injective ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩) b
        ⟨2 * (i / 16) + i % 2, by omega⟩
      rw [← permuteAt_outside (colIndex ⟨(2 * c + 1) % 8, Nat.mod_lt _ (by decide)⟩) _ _
        (fun j' => cols_disjoint.disj _ _ j' _
          (fun h => by have := congrArg Fin.val h; simp only at this; omega)), ← ec] at this
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      simpa only [colIndex, Fin.getElem_fin, ← ec, hv] using this
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      have := permuteAt_outside (colIndex ⟨(2 * c + 1) % 8, Nat.mod_lt _ (by decide)⟩)
        (permuteAt (colIndex ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩) b) ⟨i, hi⟩
        (fun j' h => by have := congrArg Fin.val h; simp only [colIndex] at this; omega)
      rw [permuteAt_outside (colIndex ⟨2 * c % 8, Nat.mod_lt _ (by decide)⟩) b ⟨i, hi⟩ (fun j' h => by
          have := congrArg Fin.val h; simp only [colIndex] at this; omega)] at this
      simpa only [Fin.getElem_fin] using this

end VG.Proof.Argon2