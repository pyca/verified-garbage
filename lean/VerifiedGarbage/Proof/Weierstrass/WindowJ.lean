import VerifiedGarbage.Proof.Weierstrass.Window
import VerifiedGarbage.Proof.Weierstrass.Booth
import VerifiedGarbage.Proof.Weierstrass.WinJacMath

/-!
# Signed windows in Jacobian coordinates, on any target

The window method of `Window.lean` with `R` in Jacobian coordinates and the
entries added by an addition that fails for equal points (and, but for the
mixed addition, opposite ones).

When the curve has prime order `n` (`PrimeOrder`), a point `P ≠ O`'s integer
multiples agree only for integers congruent modulo `n`
(`PrimeOrder.zmul_eq`). Iteration `j` adds `[d_j]P` (`|d_j| ≤ 8`) to
`[16 e]P` with `e = winE k J (j + 1)`, so as long as `16 e + 8 < n` its
operands are neither equal nor opposite unless `[16 e]P = O` (`win_sep`); the
multiples `winE` only shrink as `j` grows (`winE_le_of_le`), so one bound
for `j = 1` serves every iteration but the last.
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

variable {C : Curve}

/-! ## Multiples of a point of prime order -/

/-- In a group of prime order (`PrimeOrder`), integer multiples of a point
`P ≠ O` less than `n` apart agree only if equal. -/
theorem PrimeOrder.zmul_eq (hO : PrimeOrder C) (hC : Law C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) {a b : Int} (hab : (a - b).natAbs < C.n) (h : zmul a P = zmul b P) :
    a = b := by
  have hd := Window5.zmul_dvd hC hO hP hP0 h
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast] at hd
  have := Nat.eq_zero_of_dvd_of_lt hd hab
  omega

theorem winPt_zmul (P : Point C) (k j : Nat) :
    winPt C P k j = zmul ((nib k j : Int) - 8) P := by
  unfold winPt zmul
  split
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]; congr 1; omega
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; congr 2; omega

/-- Iteration `j`'s operands, `[16 e]P` for `e = winE k J (j + 1)` and the
point of digit `j`, are neither equal nor opposite if `16 e + 8 < n` and
`[16 e]P ≠ O`. -/
theorem win_sep (hC : Law C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) {k J j : Nat} (hb : 16 * winE k J (j + 1) + 8 < C.n)
    (hR : mul (16 * winE k J (j + 1)) P ≠ .infinity) :
    mul (16 * winE k J (j + 1)) P ≠ winPt C P k j ∧
      Spec.Weierstrass.add (mul (16 * winE k J (j + 1)) P) (winPt C P k j) ≠ .infinity := by
  have hn := nib_lt k j
  generalize winE k J (j + 1) = e at hb hR
  have h0 : e ≠ 0 := by
    rintro rfl
    exact hR (by rw [Nat.mul_zero, Spec.Weierstrass.mul]; simp)
  rw [winPt_zmul, ← zmul_natCast]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := hO.zmul_eq hC hP hP0 (by omega) h
    omega
  · rw [hC.add_zmul hP, show (.infinity : Point C) = zmul 0 P by
      rw [zmul, ite_eq_left_of_eq_true _ _ (eq_true (Int.le_refl _))]; simp [Spec.Weierstrass.mul]] at h
    have := hO.zmul_eq hC hP hP0 (by omega) h
    omega

/-! ## The multiples shrink -/

theorem winE_succ_le {k J j : Nat} (hk : 8 * geom J ≤ k) (hj : j < J) :
    winE k J (j + 1) ≤ winE k J j := by
  have := winE_step hk hj
  have := nib_lt k j
  omega

theorem winE_le_of_le {k J : Nat} (hk : 8 * geom J ≤ k) {j : Nat} :
    ∀ {j'}, j ≤ j' → j' ≤ J → winE k J j' ≤ winE k J j
  | j', h, hJ => by
    rcases Nat.eq_or_lt_of_le h with rfl | h
    · exact Nat.le_refl _
    · obtain ⟨i, rfl⟩ : ∃ i, j' = i + 1 := ⟨j' - 1, by omega⟩
      exact Nat.le_trans (winE_succ_le hk (by omega)) (winE_le_of_le hk (by omega) (by omega))

/-- The multiples of a recoded scalar `d + 8 Σ_{i<J} 16^i`: `⌊(d + 8 Σ_{i<j} 16^i) / 16^j⌋`. -/
theorem winE_recode {d J j : Nat} (hj : j ≤ J) :
    winE (d + 8 * geom J) J j = (d + 8 * geom j) / 16 ^ j := by
  have hg := geom_add j (J - j)
  rw [Nat.add_sub_cancel' hj] at hg
  have hpos : 0 < 16 ^ j := Nat.pow_pos (by decide)
  have e : d + 8 * geom J = (d + 8 * geom j) + 16 ^ j * (8 * geom (J - j)) := by
    rw [hg]; grind
  rw [winE, e, Nat.add_mul_div_left _ _ hpos]
  exact Nat.add_sub_cancel _ _

/-- The bound `windowJ_ok` needs, for scalars below `2^b`. -/
theorem winE_two_bound {d J b n : Nat} (hJ : 2 ≤ J) (hd : d < 2 ^ b)
    (hb : 16 * ((2 ^ b + 135) / 256) + 8 < n) : 16 * winE (d + 8 * geom J) J 2 + 8 < n := by
  rw [winE_recode hJ]
  have : (d + 8 * geom 2) / 16 ^ 2 ≤ (2 ^ b + 135) / 256 :=
    Nat.div_le_div_right (show d + 8 * geom 2 ≤ 2 ^ b + 135 by
      show d + 8 * (0 + 1 + 16) ≤ _; omega)
  omega

end VG.Proof.Weierstrass
