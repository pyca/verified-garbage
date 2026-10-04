import VerifiedGarbage.Proof.Weierstrass.Comb
import VerifiedGarbage.Proof.Weierstrass.Complete

/-!
# Checking a comb's tables against the group law

`chordOk` and `tangentOk` check, with `Nat` arithmetic modulo `p` and no
inverse, that `(x₃, y₃)` is the sum of two affine points of the curve by the
chord or the tangent (`add_of_chordOk`, `add_of_tangentOk`), so the kernel
can check a table of thousands of points quickly. `combOk_of_check` builds
`CombOk` from such checks: within table `j`, entry `m + 1` is entry `m` plus
entry `0`; entry `0` of table `j + 1` is twice entry `7` of table `j`
(`16 · 16^j = 2 · 8 · 16^j`); and the start is the sum of the entries `7`,
through the given partial sums.
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

variable {C : Curve}

/-- `(x₃, y₃) = (x₁, y₁) + (x₂, y₂)` by the chord, for `x₁ ≠ x₂`, checked
without inverses: `(x₃ + x₁ + x₂)(x₂ - x₁)² = (y₂ - y₁)²` and
`(y₃ + y₁)(x₂ - x₁) = (y₂ - y₁)(x₁ - x₃)`, modulo `p`. -/
def chordOk (p : Nat) (x1 y1 x2 y2 x3 y3 : Nat) : Bool :=
  x1 != x2 &&
  (x3 + x1 + x2) * ((x2 + p - x1) * (x2 + p - x1)) % p == (y2 + p - y1) * (y2 + p - y1) % p &&
  (y3 + y1) * (x2 + p - x1) % p == (y2 + p - y1) * (x1 + p - x3) % p

/-- `(x₃, y₃) = 2 (x₁, y₁)` by the tangent, for `2 y₁ ≠ 0`, checked without
inverses: `(x₃ + 2x₁)(2y₁)² = (3x₁² + a)²` and
`(y₃ + y₁)(2y₁) = (3x₁² + a)(x₁ - x₃)`, modulo `p`. -/
def tangentOk (p a : Nat) (x1 y1 x3 y3 : Nat) : Bool :=
  2 * y1 % p != 0 &&
  (x3 + 2 * x1) * (2 * y1 * (2 * y1)) % p == (3 * x1 * x1 + a) * (3 * x1 * x1 + a) % p &&
  (y3 + y1) * (2 * y1) % p == (3 * x1 * x1 + a) * (x1 + p - x3) % p

section
variable [Fact C.p.Prime]

/-- An affine point with `Nat` coordinates. -/
def ptN (C : Curve) (q : Nat × Nat) : Point C := .affine (Fin.ofNat C.p q.1) (Fin.ofNat C.p q.2)

theorem natCast_eq_of_mod {a b : Nat} (h : a % C.p = b % C.p) : (a : ZMod C.p) = (b : ZMod C.p) :=
  (ZMod.natCast_eq_natCast_iff' a b C.p).mpr h

theorem cast_sub_p {a b : Nat} (h : b ≤ a + C.p) : ((a + C.p - b : Nat) : ZMod C.p) = a - b := by
  rw [Nat.cast_sub h, Nat.cast_add, ZMod.natCast_self, add_zero]

theorem add_of_chordOk (hp : 2 < C.p) {x1 y1 x2 y2 x3 y3 : Nat} (h1 : x1 < C.p) (h2 : x2 < C.p)
    (hy1 : y1 < C.p) (h3 : x3 < C.p)
    (h : chordOk C.p x1 y1 x2 y2 x3 y3 = true) :
    add (ptN C (x1, y1)) (ptN C (x2, y2)) = ptN C (x3, y3) := by
  simp only [chordOk, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨hne, hx⟩, hy⟩ := h
  have hxne : (Fin.ofNat C.p x1 : Fe C) ≠ Fin.ofNat C.p x2 := by
    intro e
    have := congrArg Fin.val e
    simp only [Fin.val_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
    exact hne this
  rw [ptN, ptN, add_chord hxne, ptN]
  have hd : toF (Fin.ofNat C.p x2) - toF (Fin.ofNat C.p x1) ≠ 0 :=
    fun e => hxne (toF_injective (sub_eq_zero.mp e)).symm
  have hl := toF_chord_slope hp (y₁ := Fin.ofNat C.p y1) (y₂ := Fin.ofNat C.p y2) hxne
  have ex := natCast_eq_of_mod hx
  have ey := natCast_eq_of_mod hy
  have c1 : ((x2 + C.p - x1 : Nat) : ZMod C.p) = x2 - x1 := cast_sub_p (by omega)
  have c2 : ((y2 + C.p - y1 : Nat) : ZMod C.p) = y2 - y1 := cast_sub_p (by omega)
  have c3 : ((x1 + C.p - x3 : Nat) : ZMod C.p) = x1 - x3 := cast_sub_p (by omega)
  simp only [Nat.cast_mul, Nat.cast_add, c1, c2, c3] at ex ey
  generalize (Fin.ofNat C.p y2 - Fin.ofNat C.p y1) * inv (Fin.ofNat C.p x2 - Fin.ofNat C.p x1) = L
    at hl ⊢
  simp only [toF_ofNat] at hl hd
  set l := toF L
  have hx3 : (x3 : ZMod C.p) = l * l - x1 - x2 := by
    have hsq : (l * l - x1 - x2 - (x3 : ZMod C.p)) * ((x2 : ZMod C.p) - x1) ^ 2 = 0 := by
      linear_combination (l * ((x2 : ZMod C.p) - x1) + ((y2 : ZMod C.p) - y1)) * hl - ex
    rcases mul_eq_zero.mp hsq with h0 | h0
    · linear_combination -h0
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h0) hd
  have hy3 : (y3 : ZMod C.p) = l * (x1 - x3) - y1 := by
    have hm : ((y3 : ZMod C.p) + y1 - l * (x1 - x3)) * ((x2 : ZMod C.p) - x1) = 0 := by
      linear_combination ey - ((x1 : ZMod C.p) - x3) * hl
    rcases mul_eq_zero.mp hm with h0 | h0
    · linear_combination h0
    · exact absurd h0 hd
  congr 1
  · apply toF_injective
    simp only [toF_sub, toF_mul, toF_ofNat]
    rw [hx3]
  · apply toF_injective
    simp only [toF_sub, toF_mul, toF_ofNat]
    rw [hy3, hx3]

theorem add_of_tangentOk (hp : 2 < C.p) {x1 y1 x3 y3 : Nat}
    (h3 : x3 < C.p) (h : tangentOk C.p C.a x1 y1 x3 y3 = true) :
    add (ptN C (x1, y1)) (ptN C (x1, y1)) = ptN C (x3, y3) := by
  simp only [tangentOk, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨hne, hx⟩, hy⟩ := h
  have h2y : (2 : ZMod C.p) * y1 ≠ 0 := by
    intro e
    have := (ZMod.natCast_eq_natCast_iff' (2 * y1) 0 C.p).mp (by push_cast; exact e)
    simp only [Nat.zero_mod] at this
    exact hne this
  have hyy : (Fin.ofNat C.p y1 : Fe C) ≠ -Fin.ofNat C.p y1 := by
    intro e
    apply h2y
    have := congrArg toF e
    rw [toF_neg, toF_ofNat] at this
    linear_combination this
  rw [ptN, add_tangent hyy, ptN]
  have hl := toF_tangent_slope hp (x₁ := Fin.ofNat C.p x1) (two_mul_ne_zero hyy)
  have ex := natCast_eq_of_mod hx
  have ey := natCast_eq_of_mod hy
  have c3 : ((x1 + C.p - x3 : Nat) : ZMod C.p) = x1 - x3 := cast_sub_p (by omega)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, c3] at ex ey
  generalize (3 * Fin.ofNat C.p x1 * Fin.ofNat C.p x1 + Fin.ofNat C.p C.a) *
    inv (2 * Fin.ofNat C.p y1) = L at hl ⊢
  simp only [toF_ofNat] at hl
  set l := toF L
  have hx3 : (x3 : ZMod C.p) = l * l - 2 * x1 := by
    have hsq : (l * l - 2 * x1 - (x3 : ZMod C.p)) * (2 * (y1 : ZMod C.p)) ^ 2 = 0 := by
      linear_combination (l * (2 * (y1 : ZMod C.p)) + (3 * (x1 : ZMod C.p) ^ 2 + C.a)) * hl - ex
    rcases mul_eq_zero.mp hsq with h0 | h0
    · linear_combination -h0
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h0) h2y
  have hy3 : (y3 : ZMod C.p) = l * (x1 - x3) - y1 := by
    have hm : ((y3 : ZMod C.p) + y1 - l * (x1 - x3)) * (2 * (y1 : ZMod C.p)) = 0 := by
      linear_combination ey - ((x1 : ZMod C.p) - x3) * hl
    rcases mul_eq_zero.mp hm with h0 | h0
    · linear_combination h0
    · exact absurd h0 h2y
  congr 1
  · apply toF_injective
    simp only [toF_sub, toF_mul, toF_ofNat, toF_ofNat' 2]
    rw [hx3]
  · apply toF_injective
    simp only [toF_sub, toF_mul, toF_ofNat, toF_ofNat' 2]
    rw [hy3, hx3]

/-- `[m 16^j]G` from the checks of row `j`, given `[16^j]G`. -/
theorem row_mul (hC : Law C) (hp : 2 < C.p) (hG : onCurve C (G C) = true) {row : List (Nat × Nat)}
    {j : Nat} (h0 : mul (16 ^ j) (G C) = ptN C (row.getD 0 (0, 0)))
    (hlt : ∀ m < 8, (row.getD m (0, 0)).1 < C.p ∧ (row.getD m (0, 0)).2 < C.p)
    (ht : tangentOk C.p C.a (row.getD 0 (0, 0)).1 (row.getD 0 (0, 0)).2 (row.getD 1 (0, 0)).1
      (row.getD 1 (0, 0)).2 = true)
    (hc : ∀ m < 6, chordOk C.p (row.getD (m + 1) (0, 0)).1 (row.getD (m + 1) (0, 0)).2
      (row.getD 0 (0, 0)).1 (row.getD 0 (0, 0)).2 (row.getD (m + 2) (0, 0)).1
      (row.getD (m + 2) (0, 0)).2 = true) :
    ∀ m < 8, mul ((m + 1) * 16 ^ j) (G C) = ptN C (row.getD m (0, 0)) := by
  intro m hm
  induction m with
  | zero => rw [Nat.zero_add, Nat.one_mul]; exact h0
  | succ m ih =>
    rw [show (m + 1 + 1) * 16 ^ j = (m + 1) * 16 ^ j + 16 ^ j by rw [Nat.add_mul, Nat.one_mul],
      ← hC.add_mul_mul hG, ih (by omega), h0]
    cases m with
    | zero =>
      rw [Nat.zero_add] at *
      exact add_of_tangentOk hp (hlt 1 (by decide)).1 ht
    | succ m =>
      exact add_of_chordOk hp (hlt _ (by omega)).1 (hlt 0 (by decide)).1 (hlt _ (by omega)).2
        (hlt _ (by omega)).1 (hc m (by omega))

end

/-- The checks of a comb's `J` tables of `8` entries and of its start, through
the partial sums `sums` of the entries `7`. -/
def combChecks (p a : Nat) (g : Nat × Nat) (J : Nat) (tbl : List (List (Nat × Nat)))
    (sums : List (Nat × Nat)) (start : Nat × Nat) : Bool :=
  tbl.length == J && 1 ≤ J &&
  (List.range J).all (fun j => (tbl.getD j []).length == 8 &&
    (List.range 8).all fun m => decide ((combAt tbl j m).1 < p) && decide ((combAt tbl j m).2 < p)) &&
  combAt tbl 0 0 == g &&
  (List.range J).all (fun j =>
    (j == 0 || tangentOk p a (combAt tbl (j - 1) 7).1 (combAt tbl (j - 1) 7).2 (combAt tbl j 0).1
      (combAt tbl j 0).2) &&
    tangentOk p a (combAt tbl j 0).1 (combAt tbl j 0).2 (combAt tbl j 1).1 (combAt tbl j 1).2 &&
    (List.range 6).all fun m => chordOk p (combAt tbl j (m + 1)).1 (combAt tbl j (m + 1)).2
      (combAt tbl j 0).1 (combAt tbl j 0).2 (combAt tbl j (m + 2)).1 (combAt tbl j (m + 2)).2) &&
  sums.getD 0 (0, 0) == combAt tbl 0 7 &&
  (List.range (J - 1)).all (fun j => chordOk p (sums.getD j (0, 0)).1 (sums.getD j (0, 0)).2
    (combAt tbl (j + 1) 7).1 (combAt tbl (j + 1) 7).2 (sums.getD (j + 1) (0, 0)).1
    (sums.getD (j + 1) (0, 0)).2 &&
    decide ((sums.getD (j + 1) (0, 0)).1 < p) && decide ((sums.getD (j + 1) (0, 0)).2 < p)) &&
  sums.getD (J - 1) (0, 0) == start

theorem geom_succ' (j : Nat) : geom (j + 1) = geom j + 16 ^ j := rfl

/-- The checks give the facts the comb needs of its tables. -/
theorem combOk_of_check [Fact C.p.Prime] (hC : Law C) (hp : 2 < C.p)
    (hG : onCurve C (G C) = true) {J : Nat} {tbl : List (List (Nat × Nat))}
    {sums : List (Nat × Nat)} {start : Nat × Nat}
    (h : combChecks C.p C.a (C.gx, C.gy) J tbl sums start = true) : CombOk C J tbl start := by
  simp only [combChecks, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hlen, hJ⟩, hrows⟩, hg⟩, hchk⟩, hs0⟩, hsums⟩, hlast⟩ := h
  have hlt : ∀ j < J, ∀ m < 8, (combAt tbl j m).1 < C.p ∧ (combAt tbl j m).2 < C.p :=
    fun j hj m hm => (hrows j hj).2 m hm
  have entries : ∀ j < J, ∀ m < 8, mul ((m + 1) * 16 ^ j) (G C) = ptN C (combAt tbl j m) := by
    intro j
    induction j with
    | zero =>
      intro hj
      refine row_mul hC hp hG (row := tbl.getD 0 []) ?_ (hlt 0 hj) (hchk 0 hj).1.2
        (hchk 0 hj).2
      rw [Nat.pow_zero, mul_one_pt]
      show G C = ptN C (combAt tbl 0 0)
      rw [hg]; rfl
    | succ j ih =>
      intro hj
      refine row_mul hC hp hG (row := tbl.getD (j + 1) []) ?_ (hlt _ hj) (hchk _ hj).1.2
        (hchk _ hj).2
      have h7 := ih (by omega) 7 (by decide)
      have ht := (hchk (j + 1) hj).1.1
      simp only [Nat.add_one_ne_zero, Nat.add_sub_cancel] at ht
      replace ht := ht.resolve_left id
      rw [show 16 ^ (j + 1) = (7 + 1) * 16 ^ j + (7 + 1) * 16 ^ j by rw [Nat.pow_succ]; omega,
        ← hC.add_mul_mul hG, h7]
      exact add_of_tangentOk hp (hlt (j + 1) hj 0 (by decide)).1 ht
  have hsum : ∀ j < J, mul (8 * geom (j + 1)) (G C) = ptN C (sums.getD j (0, 0)) ∧
      (sums.getD j (0, 0)).1 < C.p ∧ (sums.getD j (0, 0)).2 < C.p := by
    intro j
    induction j with
    | zero =>
      intro hj
      rw [hs0]
      refine ⟨?_, hlt 0 hj 7 (by decide)⟩
      have := entries 0 hj 7 (by decide)
      simp only [Nat.pow_zero, Nat.mul_one] at this
      rw [show 8 * geom (0 + 1) = 8 by rfl]
      exact this
    | succ j ih =>
      intro hj
      obtain ⟨hm, hl1, hl2⟩ := ih (by omega)
      obtain ⟨⟨hc, hb1⟩, hb2⟩ := hsums j (by omega)
      refine ⟨?_, hb1, hb2⟩
      rw [geom_succ', Nat.mul_add, ← hC.add_mul_mul hG, hm,
        show 8 * 16 ^ (j + 1) = (7 + 1) * 16 ^ (j + 1) by rfl, entries (j + 1) hj 7 (by decide)]
      exact add_of_chordOk hp hl1 (hlt (j + 1) hj 7 (by decide)).1 hl2 hb1 hc
  have hst := hsum (J - 1) (by omega)
  rw [Nat.sub_add_cancel hJ, hlast] at hst
  exact ⟨hlen, fun j hj => (hrows j hj).1, hlt, entries, ⟨hst.2.1, hst.2.2⟩, hst.1⟩

end VG.Proof.Weierstrass
