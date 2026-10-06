import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.CombW

/-!
# Checking a `w`-bit comb's tables against the group law

For tables of `H = 2^(w-1) ≥ 2` entries, from the group law's checks of
chords and tangents without inverses (`Law.chord`, `Law.tangent`): within table `j`, entry `m + 1` is entry `m` plus
entry `0` (by the tangent for `m = 0`, else by the chord); entry `0` of table
`j + 1` is twice entry `H - 1` of table `j` (`2^(w(j+1)) = 2 H 2^(wj)`); and
the start is the sum of the entries `H - 1`, through the given partial sums
(`combOkW_of_check`).
-/

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
      ← hC.add_mul_mul hG, ih (by omega), h0]
    cases m with
    | zero =>
      rw [Nat.zero_add] at *
      exact hC.tangent (hlt 1 hm).1 (ht (by omega))
    | succ m =>
      exact hC.chord (hlt _ (by omega)).1 (hlt 0 (by omega)).1 (hlt _ (by omega)).2
        (hlt _ (by omega)).1 (hc m (by omega))


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
    rw [show w = w - 1 + 1 by omega, Nat.pow_succ, Nat.add_sub_cancel]; omega
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
      have h7 := ih (by omega) (2 ^ (w - 1) - 1) (by omega)
      have ht := (hchk (j + 1) hj).1.1
      simp only [Nat.add_one_ne_zero, Nat.add_sub_cancel] at ht
      replace ht := ht.resolve_left id
      rw [Nat.sub_add_cancel (Nat.two_pow_pos _)] at h7
      rw [pow_w_succ, hHw, Nat.mul_add, Nat.mul_comm (2 ^ (w * j)) (2 ^ (w - 1)),
        ← hC.add_mul_mul hG, h7]
      exact hC.tangent (hlt (j + 1) hj 0 (Nat.two_pow_pos _)).1 ht
  have hlast' : ∀ j < J, mul (2 ^ (w - 1) * 2 ^ (w * j)) (G C) =
      ptN C (combAt tbl j (2 ^ (w - 1) - 1)) := fun j hj => by
    have := entries j hj (2 ^ (w - 1) - 1) (by omega)
    rwa [Nat.sub_add_cancel (Nat.two_pow_pos _)] at this
  have hsum : ∀ j < J, mul (2 ^ (w - 1) * geomW w (j + 1)) (G C) = ptN C (sums.getD j (0, 0)) ∧
      (sums.getD j (0, 0)).1 < C.p ∧ (sums.getD j (0, 0)).2 < C.p := by
    intro j
    induction j with
    | zero =>
      intro hj
      rw [hs0]
      refine ⟨?_, hlt 0 hj _ (by omega)⟩
      have := hlast' 0 hj
      simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one] at this
      rw [show 2 ^ (w - 1) * geomW w (0 + 1) = 2 ^ (w - 1) by simp [geomW]]
      exact this
    | succ j ih =>
      intro hj
      obtain ⟨hm, hl1, hl2⟩ := ih (by omega)
      obtain ⟨⟨hc, hb1⟩, hb2⟩ := hsums j (by omega)
      refine ⟨?_, hb1, hb2⟩
      rw [show geomW w (j + 1 + 1) = geomW w (j + 1) + 2 ^ (w * (j + 1)) from rfl, Nat.mul_add,
        ← hC.add_mul_mul hG, hm, hlast' (j + 1) hj]
      exact hC.chord hl1 (hlt (j + 1) hj _ (by omega)).1 hl2 hb1 hc
  have hst := hsum (J - 1) (by omega)
  rw [Nat.sub_add_cancel hJ, hlast] at hst
  exact ⟨hlen, fun j hj => (hrows j hj).1, hlt, entries, ⟨hst.2.1, hst.2.2⟩, hst.1⟩

end VG.Proof.Weierstrass
