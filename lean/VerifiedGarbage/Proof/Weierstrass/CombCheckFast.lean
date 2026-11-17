module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.CombW

/-! ### `Weierstrass.CombCheckW`, which this module and modules that import it used -/

section

/-!
# Checking a `w`-bit comb's tables against the group law

For tables of `H = 2^(w-1) ≥ 2` entries, from the group law's checks of
chords and tangents without inverses (`Law.chord`, `Law.tangent`): within table `j`, entry `m + 1` is entry `m` plus
entry `0` (by the tangent for `m = 0`, else by the chord); entry `0` of table
`j + 1` is twice entry `H - 1` of table `j` (`2^(w(j+1)) = 2 H 2^(wj)`); and
the start is the sum of the entries `H - 1`, through the given partial sums
(`combOkW_of_check`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

variable {C : Curve}

/-- `[m 2^(wj)]G` from the checks of row `j` (of `H` entries), given `[2^(wj)]G`. -/
theorem rowW_mul (hC : Law C) (hG : onCurve C (G C) = true) {H : Nat}
    {row : List (Nat × Nat)} {b : Nat} (h0 : mul b (G C) = ptN C (row.getD 0 (0, 0)))
    (hlt : ∀ m < H, (row.getD m (0, 0)).1 < C.p ∧ (row.getD m (0, 0)).2 < C.p)
    (ht : 2 ≤ H → tangentOk C.p C.a (row.getD 0 (0, 0)).1 (row.getD 0 (0, 0)).2
      (row.getD 1 (0, 0)).1 (row.getD 1 (0, 0)).2 = true)
    (hc : ∀ m < H - 2, chordOk C.p (row.getD (m + 1) (0, 0)).1 (row.getD (m + 1) (0, 0)).2
      (row.getD 0 (0, 0)).1 (row.getD 0 (0, 0)).2 (row.getD (m + 2) (0, 0)).1
      (row.getD (m + 2) (0, 0)).2 = true) :
    ∀ m < H, mul ((m + 1) * b) (G C) = ptN C (row.getD m (0, 0)) := by
  intro m hm
  induction m with
  | zero => rw [Nat.zero_add, Nat.one_mul]; exact h0
  | succ m ih =>
    rw [show (m + 1 + 1) * b = (m + 1) * b + b by rw [Nat.add_mul, Nat.one_mul],
      ← hC.add_mul_mul hG, ih (by omega_using [hm]), h0]
    cases m with
    | zero =>
      rw [Nat.zero_add] at *
      exact hC.tangent (hlt 1 hm).1 (ht (by omega_using [hm]))
    | succ m =>
      exact hC.chord (hlt _ (by omega_using [hm])).1 (hlt 0 (by omega_using [hm])).1 (hlt _ (by omega_using [hm])).2
        (hlt _ (by omega_using [hm])).1 (hc m (by omega_using [hm]))


/-- The checks of a comb's `J` tables of `H` entries and of its start, through
the partial sums `sums` of the entries `H - 1`. -/
def combChecksW (p a : Nat) (g : Nat × Nat) (H J : Nat) (tbl : List (List (Nat × Nat)))
    (sums : List (Nat × Nat)) (start : Nat × Nat) : Bool :=
  tbl.length == J && 1 ≤ J && 2 ≤ H &&
  (List.range J).all (fun j => (tbl.getD j []).length == H &&
    (List.range H).all fun m => decide ((combAt tbl j m).1 < p) && decide ((combAt tbl j m).2 < p)) &&
  combAt tbl 0 0 == g &&
  (List.range J).all (fun j =>
    (j == 0 || tangentOk p a (combAt tbl (j - 1) (H - 1)).1 (combAt tbl (j - 1) (H - 1)).2
      (combAt tbl j 0).1 (combAt tbl j 0).2) &&
    tangentOk p a (combAt tbl j 0).1 (combAt tbl j 0).2 (combAt tbl j 1).1 (combAt tbl j 1).2 &&
    (List.range (H - 2)).all fun m => chordOk p (combAt tbl j (m + 1)).1 (combAt tbl j (m + 1)).2
      (combAt tbl j 0).1 (combAt tbl j 0).2 (combAt tbl j (m + 2)).1 (combAt tbl j (m + 2)).2) &&
  sums.getD 0 (0, 0) == combAt tbl 0 (H - 1) &&
  (List.range (J - 1)).all (fun j => chordOk p (sums.getD j (0, 0)).1 (sums.getD j (0, 0)).2
    (combAt tbl (j + 1) (H - 1)).1 (combAt tbl (j + 1) (H - 1)).2 (sums.getD (j + 1) (0, 0)).1
    (sums.getD (j + 1) (0, 0)).2 &&
    decide ((sums.getD (j + 1) (0, 0)).1 < p) && decide ((sums.getD (j + 1) (0, 0)).2 < p)) &&
  sums.getD (J - 1) (0, 0) == start

/-- The checks give the facts the comb needs of its tables, for `w ≥ 2`. -/
theorem combOkW_of_check (hC : Law C)
    (hG : onCurve C (G C) = true) {w J : Nat} (hw : 2 ≤ w) {tbl : List (List (Nat × Nat))}
    {sums : List (Nat × Nat)} {start : Nat × Nat}
    (h : combChecksW C.p C.a (C.gx, C.gy) (2 ^ (w - 1)) J tbl sums start = true) :
    CombOkW C w J tbl start := by
  simp only [combChecksW, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hlen, hJ⟩, hH⟩, hrows⟩, hg⟩, hchk⟩, hs0⟩, hsums⟩, hlast⟩ := h
  have hHw : 2 ^ w = 2 ^ (w - 1) + 2 ^ (w - 1) := by
    rw [show w = w - 1 + 1 by omega_using [hw], Nat.pow_succ, Nat.add_sub_cancel]; omega_using []
  have hlt : ∀ j < J, ∀ m < 2 ^ (w - 1), (combAt tbl j m).1 < C.p ∧ (combAt tbl j m).2 < C.p :=
    fun j hj m hm => (hrows j hj).2 m hm
  have entries : ∀ j < J, ∀ m < 2 ^ (w - 1),
      mul ((m + 1) * 2 ^ (w * j)) (G C) = ptN C (combAt tbl j m) := by
    intro j
    induction j with
    | zero =>
      intro hj
      refine rowW_mul hC hG (row := tbl.getD 0 []) ?_ (hlt 0 hj) (fun _ => (hchk 0 hj).1.2)
        (hchk 0 hj).2
      rw [Nat.mul_zero, Nat.pow_zero, mul_one_pt]
      show G C = ptN C (combAt tbl 0 0)
      rw [hg]; rfl
    | succ j ih =>
      intro hj
      refine rowW_mul hC hG (row := tbl.getD (j + 1) []) ?_ (hlt _ hj)
        (fun _ => (hchk _ hj).1.2) (hchk _ hj).2
      have h7 := ih (by omega_using [hj]) (2 ^ (w - 1) - 1) (by omega_using [hH])
      have ht := (hchk (j + 1) hj).1.1
      simp only [Nat.add_one_ne_zero, Nat.add_sub_cancel] at ht
      replace ht := ht.resolve_left id
      rw [Nat.sub_add_cancel (Nat.two_pow_pos _)] at h7
      rw [pow_w_succ, hHw, Nat.mul_add, Nat.mul_comm (2 ^ (w * j)) (2 ^ (w - 1)),
        ← hC.add_mul_mul hG, h7]
      exact hC.tangent (hlt (j + 1) hj 0 (Nat.two_pow_pos _)).1 ht
  have hlast' : ∀ j < J, mul (2 ^ (w - 1) * 2 ^ (w * j)) (G C) =
      ptN C (combAt tbl j (2 ^ (w - 1) - 1)) := fun j hj => by
    have := entries j hj (2 ^ (w - 1) - 1) (by omega_using [hH])
    rwa [Nat.sub_add_cancel (Nat.two_pow_pos _)] at this
  have hsum : ∀ j < J, mul (2 ^ (w - 1) * geomW w (j + 1)) (G C) = ptN C (sums.getD j (0, 0)) ∧
      (sums.getD j (0, 0)).1 < C.p ∧ (sums.getD j (0, 0)).2 < C.p := by
    intro j
    induction j with
    | zero =>
      intro hj
      rw [hs0]
      refine ⟨?_, hlt 0 hj _ (by omega_using [hH])⟩
      have := hlast' 0 hj
      simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one] at this
      rw [show 2 ^ (w - 1) * geomW w (0 + 1) = 2 ^ (w - 1) by simp [geomW]]
      exact this
    | succ j ih =>
      intro hj
      obtain ⟨hm, hl1, hl2⟩ := ih (by omega_using [hj])
      obtain ⟨⟨hc, hb1⟩, hb2⟩ := hsums j (by omega_using [hj])
      refine ⟨?_, hb1, hb2⟩
      rw [show geomW w (j + 1 + 1) = geomW w (j + 1) + 2 ^ (w * (j + 1)) from rfl, Nat.mul_add,
        ← hC.add_mul_mul hG, hm, hlast' (j + 1) hj]
      exact hC.chord hl1 (hlt (j + 1) hj _ (by omega_using [hH])).1 hl2 hb1 hc
  have hst := hsum (J - 1) (by omega_using [hJ])
  rw [Nat.sub_add_cancel hJ, hlast] at hst
  exact ⟨hlen, fun j hj => (hrows j hj).1, hlt, entries, ⟨hst.2.1, hst.2.2⟩, hst.1⟩

end VG.Proof.Weierstrass

end

end

/-!
# Checking a comb's tables without indexing

`combChecksW` reads every entry by its indices (`combAt`), which the kernel
evaluates by walking the lists from their heads, through `List.getD`'s
instances: most of the time of its check, for large tables (14 s of P-521's
20 s). `combChecksF` checks the same facts by walking each table, the
tables and the partial sums once, and implies it (`combChecksW_of_fast`).
-/

@[expose] public section

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
      have := chordsF_getD hc.2 m (by simp at hm ⊢; omega_using [hm])
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
      have := linksF_getD hc.2 j (by simp at hj ⊢; omega_using [hj])
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
      have := sumsF_getD hc.2 j (by simp at hj ⊢; omega_using [hj]) (by simp at hr ⊢; omega_using [hr])
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
    hrows _ (getD_mem_of_lt (by omega_using [hlen, hj]))
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
      | succ j => exact .inr (linksF_getD hlinks j (by omega_using [hlen, hj]))
    · have := chordsF_getD hc m (by rw [List.length_tail]; omega_using [hl, hm])
      simpa only [combAt, List.getD_eq_getElem?_getD, List.getElem?_tail] using this
  · have := sumsF_getD hsums j (by omega_using [hS, hj]) (by rw [List.length_tail]; omega_using [hlen, hj])
    simpa only [combAt, List.getD_eq_getElem?_getD, List.getElem?_tail, and_assoc] using this

end VG.Proof.Weierstrass
