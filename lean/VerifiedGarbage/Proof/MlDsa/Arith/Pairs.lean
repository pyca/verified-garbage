/-!
# Updating disjoint pairs of a vector

`pairsApply f v ps` updates the pairs `ps` of entries of `v` in turn, each pair
`(i, j)` to `f v[i] v[j]`. When no two pairs share an entry, entry `k` of the
result depends only on the pair containing `k`, if any (`pairsApply_get`): a
proof about a schedule of butterflies on a register bank then decides which
pair holds each entry, a finite fact, rather than evaluating the schedule for
each entry.
-/

namespace VG.Proof.MlDsa.Pairs

variable {α : Type} {n : Nat}

/-- Updates pairs of entries of `v` in turn: `(i, j)` sets `v[i], v[j]` to `f v[i] v[j]`. -/
def pairsApply (f : α → α → α × α) (v : Vector α n) : List (Fin n × Fin n) → Vector α n
  | [] => v
  | (i, j) :: ps => pairsApply f ((v.set i.val (f v[i.val] v[j.val]).1).set j.val (f v[i.val] v[j.val]).2) ps

/-- The pair of `ps` that contains `k`. -/
def pairOf (ps : List (Fin n × Fin n)) (k : Fin n) : Option (Fin n × Fin n) :=
  ps.find? fun p => p.1 == k || p.2 == k

/-- The entries of `ps`, in order. -/
def entries (ps : List (Fin n × Fin n)) : List (Fin n) := ps.flatMap fun p => [p.1, p.2]

theorem pairOf_mem {ps : List (Fin n × Fin n)} {k : Fin n} {p : Fin n × Fin n} (h : pairOf ps k = some p) :
    p.1 ∈ entries ps ∧ p.2 ∈ entries ps := by
  have hm := List.mem_of_find?_eq_some h
  exact ⟨List.mem_flatMap.mpr ⟨p, hm, by simp⟩, List.mem_flatMap.mpr ⟨p, hm, by simp⟩⟩

theorem pairOf_none {ps : List (Fin n × Fin n)} {k : Fin n} (hk : k ∉ entries ps) : pairOf ps k = none := by
  apply List.find?_eq_none.mpr
  intro p hp
  have h1 : p.1 ≠ k := fun e => hk (List.mem_flatMap.mpr ⟨p, hp, by simp [e]⟩)
  have h2 : p.2 ≠ k := fun e => hk (List.mem_flatMap.mpr ⟨p, hp, by simp [e]⟩)
  simp [h1, h2]

/-- Entry `k` after updating pairs that share no entry. -/
theorem pairsApply_get (f : α → α → α × α) (v : Vector α n) {ps : List (Fin n × Fin n)}
    (hd : (entries ps).Nodup) (k : Fin n) :
    (pairsApply f v ps)[k.val] = match pairOf ps k with
      | some (i, j) => if i = k then (f v[i.val] v[j.val]).1 else (f v[i.val] v[j.val]).2
      | none => v[k.val] := by
  induction ps generalizing v with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨i, j⟩ := p
    simp only [entries, List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons,
      List.mem_cons, not_or] at hd
    obtain ⟨⟨hij, hi⟩, hj, hd⟩ := hd
    rw [pairsApply, ih _ hd]
    have hpk : pairOf ((i, j) :: ps) k = if i = k ∨ j = k then some (i, j) else pairOf ps k := by
      unfold pairOf
      rw [List.find?_cons]
      by_cases h : i = k ∨ j = k
      · have hb : (i == k || j == k) = true := by rcases h with h | h <;> simp [h]
        rw [hb, ite_eq_left_of_eq_true _ _ (eq_true h)]
      · rw [not_or] at h
        have hb : (i == k || j == k) = false := by simp [h.1, h.2]
        rw [hb, ite_eq_right_of_eq_false _ _ (eq_false (not_or.mpr h))]
    rw [hpk]
    by_cases hk : i = k ∨ j = k
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hk), pairOf_none (hk.elim (fun h => h ▸ hi) (fun h => h ▸ hj))]
      simp only [Vector.getElem_set]
      rcases hk with rfl | rfl
      · simp [Fin.val_ne_of_ne (Ne.symm hij)]
      · simp [hij]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hk)]
      rw [not_or] at hk
      cases hp : pairOf ps k with
      | none =>
        simp only [Vector.getElem_set, Fin.val_ne_of_ne hk.1, Fin.val_ne_of_ne hk.2, ite_false]
      | some q =>
        obtain ⟨a, b⟩ := q
        obtain ⟨ha, hb⟩ := pairOf_mem hp
        have h1 : i ≠ a := fun e => hi (e ▸ ha)
        have h2 : j ≠ a := fun e => hj (e ▸ ha)
        have h3 : i ≠ b := fun e => hi (e ▸ hb)
        have h4 : j ≠ b := fun e => hj (e ▸ hb)
        simp only [Vector.getElem_set, Fin.val_ne_of_ne h1, Fin.val_ne_of_ne h2, Fin.val_ne_of_ne h3,
          Fin.val_ne_of_ne h4, ite_false]

end VG.Proof.MlDsa.Pairs
