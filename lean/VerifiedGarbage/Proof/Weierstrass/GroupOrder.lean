import VerifiedGarbage.Proof.Weierstrass.Group
import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.SetTheory.Cardinal.Finite

/-!
# A curve of prime order, from the order of its base point

The points of a curve over `GF(p)` form a finite abelian group `E` (Mathlib's
points of `wcC C`, which `toW` maps the specification's to), with at most
`2p + 1` elements: `O`, and for each `x` at most two `y` (`y` and `-y`),
which `card_le` tells apart by which of `y` and `-y` is the smaller
integer. If the base point `G` has prime order `n` (`[n]G = O`), then
`n ∣ #E`; if moreover `2p + 1 < 3n`, `#E` is `n` or `2n`, and `2n` is ruled
out by Cauchy's theorem, since a curve with no point of order 2 (`Good`)
has no element of order 2. So `#E = n` is prime, and every point but `O`
has order `n` (`primeOrder_of`).
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass WeierstrassCurve.Affine

variable {C : Curve} [Fact C.p.Prime]

/-- A point of `E` as `O` (`none`) or its `x` and whether `y` is the smaller
of `y` and `-y`. -/
private def code : (wcC C).Point → Option (ZMod C.p × Bool)
  | .zero => none
  | .some x y _ => some (x, decide (y.val < (-y).val))

private theorem code_injective : Function.Injective (code (C := C)) := by
  intro P Q h
  match P, Q with
  | .zero, .zero => rfl
  | .zero, .some .. => exact absurd h (by simp [code])
  | .some .., .zero => exact absurd h (by simp [code])
  | .some x₁ y₁ h₁, .some x₂ y₂ h₂ =>
    simp only [code, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, hb⟩ := h
    have hy : y₁ = y₂ := by
      rcases Y_eq_of_X_eq h₁.1 h₂.1 rfl with hy | hy
      · exact hy
      · rw [negY_wcC] at hy
        subst hy
        rw [neg_neg] at hb
        have hv : (-y₂).val = y₂.val := by
          refine Nat.le_antisymm (Nat.not_lt.mp fun hlt => ?_) (Nat.not_lt.mp fun hlt => ?_)
          · simp [hlt, Nat.not_lt_of_gt hlt] at hb
          · simp [hlt, Nat.not_lt_of_gt hlt] at hb
        exact ZMod.val_injective _ hv
    subst hy
    rfl

instance finite_point : Finite (wcC C).Point := Finite.of_injective _ code_injective

/-- `#E ≤ 2p + 1`. -/
theorem card_le : Nat.card (wcC C).Point ≤ 2 * C.p + 1 := by
  have h := Nat.card_le_card_of_injective _ (code_injective (C := C))
  rw [Finite.card_option, Nat.card_prod, Nat.card_zmod, Nat.card_eq_fintype_card (α := Bool),
    Fintype.card_bool] at h
  omega

/-- A curve with no point of order 2 has no element of order 2. -/
theorem addOrderOf_ne_two (hC : Good C) (Q : (wcC C).Point) : addOrderOf Q ≠ 2 := by
  intro h2
  have h0 : Q ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at h2
    exact absurd h2 (by decide)
  have hQ : Q + Q = 0 := by
    rw [← two_nsmul, ← h2]
    exact addOrderOf_nsmul_eq_zero Q
  match Q, h0, hQ with
  | .zero, h0, _ => exact h0 rfl
  | .some x y h, _, hQ =>
    rw [add_eq_zero_iff_eq_neg, Point.neg_some] at hQ
    obtain ⟨-, hy⟩ := Point.some.inj hQ
    rw [negY_wcC] at hy
    have h2y : (2 : ZMod C.p) * y = 0 := by rw [two_mul]; nth_rw 1 [hy]; exact neg_add_cancel y
    rcases mul_eq_zero.mp h2y with h2y | h2y
    · exact two_ne_zero' hC.two_lt h2y
    · exact Weierstrass.y_ne_zero hC.noTwoTorsion (wc_equation.mp h.1) h2y

/-- On a curve with no point of order 2 whose base point has prime order `n`
with `2p + 1 < 3n`, every point but `O` has order `n`. -/
theorem primeOrder_of (hC : Good C) (hn : C.n.Prime) (hG : onCurve C (G C) = true)
    (hGn : mul C.n (G C) = .infinity) (hb : 2 * C.p + 1 < 3 * C.n) : PrimeOrder C := by
  have : Fact C.n.Prime := ⟨hn⟩
  -- `G` has order `n` in `E`, so `n ∣ #E`.
  have hG0 : toW hC (G C) ≠ 0 := by
    rw [G, toW_affine hC hG]; exact Point.some_ne_zero _
  have hGn' : C.n • toW hC (G C) = 0 := by
    rw [← toW_mul hC hG, hGn]; rfl
  have hdvd : C.n ∣ Nat.card (wcC C).Point :=
    addOrderOf_eq_prime hGn' hG0 ▸ addOrderOf_dvd_natCard _
  -- `#E` is `n` or `2n`, and not `2n`.
  obtain ⟨k, hk⟩ := hdvd
  have hpos : 0 < Nat.card (wcC C).Point := Nat.card_pos
  have hk3 : k < 3 := Nat.lt_of_mul_lt_mul_left (a := C.n) (by
    have := card_le (C := C); rw [hk] at this; omega)
  have hk1 : k = 1 := by
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with h | h | h
    · rw [hk, h, Nat.mul_zero] at hpos; omega
    · exact h
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨Q, hQ⟩ := exists_prime_addOrderOf_dvd_card' (G := (wcC C).Point) 2
        ⟨C.n, by rw [hk, h, Nat.mul_comm]⟩
      exact absurd hQ (addOrderOf_ne_two hC Q)
  rw [hk1, Nat.mul_one] at hk
  -- Every point but `O` has order `n`.
  intro P hP hPO m hm
  have hP0 : toW hC P ≠ 0 := fun h0 =>
    hPO (toW_inj hC hP rfl (h0.trans rfl))
  have hord : addOrderOf (toW hC P) = C.n := by
    rcases hn.eq_one_or_self_of_dvd _ (hk ▸ addOrderOf_dvd_natCard (toW hC P)) with h | h
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h) hP0
    · exact h
  rw [← hord]
  apply addOrderOf_dvd_of_nsmul_eq_zero
  rw [← toW_mul hC hP, hm]
  rfl

end VG.Proof.Weierstrass
