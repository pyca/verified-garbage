import VerifiedGarbage.Proof.Weierstrass.CombCheckW

/-!
# Checking a comb's tables without indexing

`combChecksW` reads every entry by its indices (`combAt`), which the kernel
evaluates by walking the lists from their heads, through `List.getD`'s
instances: most of the time of its check, for large tables (14 s of P-521's
20 s). `combChecksF` checks the same facts by walking each table, the
tables and the partial sums once, and implies it (`combChecksW_of_fast`).
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

/-- The chords `l[m + 1] = l[m] + (x0, y0)`, for consecutive entries of `l`. -/
def chordsF (p x0 y0 : Nat) : List (Nat × Nat) → Bool
  | e :: f :: l => chordOk p e.1 e.2 x0 y0 f.1 f.2 && chordsF p x0 y0 (f :: l)
  | _ => true

/-- A table of `H` entries below `p`, each the previous plus the first. -/
def rowF (p a H : Nat) (row : List (Nat × Nat)) : Bool :=
  row.length == H && row.all (fun e => decide (e.1 < p) && decide (e.2 < p)) &&
  tangentOk p a (row.getD 0 (0, 0)).1 (row.getD 0 (0, 0)).2 (row.getD 1 (0, 0)).1
    (row.getD 1 (0, 0)).2 &&
  chordsF p (row.getD 0 (0, 0)).1 (row.getD 0 (0, 0)).2 row.tail

/-- The first entry of each table is twice the last of the table before. -/
def linksF (p a H : Nat) : List (List (Nat × Nat)) → Bool
  | r :: s :: l => tangentOk p a (r.getD (H - 1) (0, 0)).1 (r.getD (H - 1) (0, 0)).2
      (s.getD 0 (0, 0)).1 (s.getD 0 (0, 0)).2 && linksF p a H (s :: l)
  | _ => true

/-- Each partial sum is the one before plus the last entry of the next table. -/
def sumsF (p H : Nat) : List (Nat × Nat) → List (List (Nat × Nat)) → Bool
  | s :: t :: ss, r :: rs => chordOk p s.1 s.2 (r.getD (H - 1) (0, 0)).1 (r.getD (H - 1) (0, 0)).2
      t.1 t.2 && decide (t.1 < p) && decide (t.2 < p) && sumsF p H (t :: ss) rs
  | _, _ => true

/-- `combChecksW`, by walking the lists. -/
def combChecksF (p a : Nat) (g : Nat × Nat) (H J : Nat) (tbl : List (List (Nat × Nat)))
    (sums : List (Nat × Nat)) (start : Nat × Nat) : Bool :=
  tbl.length == J && 1 ≤ J && 2 ≤ H && J ≤ sums.length && tbl.all (rowF p a H) &&
  combAt tbl 0 0 == g && linksF p a H tbl && sums.getD 0 (0, 0) == combAt tbl 0 (H - 1) &&
  sumsF p H sums tbl.tail && sums.getD (J - 1) (0, 0) == start

theorem chordsF_getD {p x0 y0 : Nat} :
    ∀ {l : List (Nat × Nat)}, chordsF p x0 y0 l = true → ∀ m, m + 1 < l.length →
      chordOk p (l.getD m (0, 0)).1 (l.getD m (0, 0)).2 x0 y0 (l.getD (m + 1) (0, 0)).1
        (l.getD (m + 1) (0, 0)).2 = true
  | [], _, _, h => absurd h (by simp)
  | [_], _, _, h => absurd h (by simp)
  | e :: f :: l, hc, m, hm => by
    simp only [chordsF, Bool.and_eq_true] at hc
    cases m with
    | zero => exact hc.1
    | succ m =>
      have := chordsF_getD hc.2 m (by simp at hm ⊢; omega)
      simpa only [List.getD_cons_succ] using this

theorem linksF_getD {p a H : Nat} :
    ∀ {tbl : List (List (Nat × Nat))}, linksF p a H tbl = true → ∀ j, j + 1 < tbl.length →
      tangentOk p a (combAt tbl j (H - 1)).1 (combAt tbl j (H - 1)).2
        (combAt tbl (j + 1) 0).1 (combAt tbl (j + 1) 0).2 = true
  | [], _, _, h => absurd h (by simp)
  | [_], _, _, h => absurd h (by simp)
  | r :: s :: l, hc, j, hj => by
    simp only [linksF, Bool.and_eq_true] at hc
    cases j with
    | zero => exact hc.1
    | succ j =>
      have := linksF_getD hc.2 j (by simp at hj ⊢; omega)
      simpa only [combAt, List.getD_cons_succ] using this

theorem sumsF_getD {p H : Nat} :
    ∀ {ss : List (Nat × Nat)} {rs : List (List (Nat × Nat))}, sumsF p H ss rs = true →
      ∀ j, j + 1 < ss.length → j < rs.length →
      chordOk p (ss.getD j (0, 0)).1 (ss.getD j (0, 0)).2 ((rs.getD j []).getD (H - 1) (0, 0)).1
        ((rs.getD j []).getD (H - 1) (0, 0)).2 (ss.getD (j + 1) (0, 0)).1
        (ss.getD (j + 1) (0, 0)).2 = true ∧
      (ss.getD (j + 1) (0, 0)).1 < p ∧ (ss.getD (j + 1) (0, 0)).2 < p
  | [], _, _, _, h, _ => absurd h (by simp)
  | [_], _, _, _, h, _ => absurd h (by simp)
  | _ :: _ :: _, [], _, _, _, h => absurd h (by simp)
  | s :: t :: ss, r :: rs, hc, j, hj, hr => by
    simp only [sumsF, Bool.and_eq_true, decide_eq_true_eq] at hc
    cases j with
    | zero => exact ⟨hc.1.1.1, hc.1.1.2, hc.1.2⟩
    | succ j =>
      have := sumsF_getD hc.2 j (by simp at hj ⊢; omega) (by simp at hr ⊢; omega)
      simpa only [List.getD_cons_succ] using this

theorem getD_mem_of_lt {α : Type} {l : List α} {j : Nat} {d : α} (h : j < l.length) :
    l.getD j d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

/-- The checks by walking the lists imply those by indices. -/
theorem combChecksW_of_fast {p a : Nat} {g : Nat × Nat} {H J : Nat}
    {tbl : List (List (Nat × Nat))} {sums : List (Nat × Nat)} {start : Nat × Nat}
    (h : combChecksF p a g H J tbl sums start = true) :
    combChecksW p a g H J tbl sums start = true := by
  simp only [combChecksF, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hlen, hJ⟩, hH⟩, hS⟩, hrows⟩, hg⟩, hlinks⟩, hs0⟩, hsums⟩, hlast⟩ := h
  have hrow : ∀ j < J, rowF p a H (tbl.getD j []) = true := fun j hj =>
    hrows _ (getD_mem_of_lt (by omega))
  simp only [combChecksW, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨hlen, hJ⟩, hH⟩, (fun j hj => ?_)⟩, hg⟩, (fun j hj => ?_)⟩, hs0⟩, (fun j hj => ?_)⟩, hlast⟩
  · have hr := hrow j hj
    simp only [rowF, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hr
    refine ⟨hr.1.1.1, fun m hm => hr.1.1.2 _ (getD_mem_of_lt (by omega))⟩
  · have hr := hrow j hj
    simp only [rowF, Bool.and_eq_true, beq_iff_eq] at hr
    obtain ⟨⟨⟨hl, -⟩, ht⟩, hc⟩ := hr
    refine ⟨⟨?_, ht⟩, fun m hm => ?_⟩
    · cases j with
      | zero => exact .inl rfl
      | succ j => exact .inr (linksF_getD hlinks j (by omega))
    · have := chordsF_getD hc m (by rw [List.length_tail]; omega)
      simpa only [combAt, List.getD_eq_getElem?_getD, List.getElem?_tail] using this
  · have := sumsF_getD hsums j (by omega) (by rw [List.length_tail]; omega)
    simpa only [combAt, List.getD_eq_getElem?_getD, List.getElem?_tail, and_assoc] using this

end VG.Proof.Weierstrass
