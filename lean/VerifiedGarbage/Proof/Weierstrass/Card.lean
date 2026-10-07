import VerifiedGarbage.Proof.Weierstrass.Group
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Every point of a prime-order curve has order `n`

For a curve the proofs apply to (`Good`: no point of order 2) whose base
point `G` has prime order `n` (`[n]G = O`), with `2p + 1 < 3n`: the curve
has `n` points, so `[n]P = O` for every point `P` of it (`Good.mul_n`).

The points over `ZMod p` are at most `2p + 1`: `O`, and for each `x` at most
the two `y` of `y² = x³ + ax + b`, `y` and `-y`, which `enc` tells apart by
the half `y` is in. `G`'s order `n` divides their number (Lagrange), which
is then `n` or `2n`; an even number would give a point of order 2 (Cauchy),
which has `y = 0`, a root of `x³ + ax + b`.
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass WeierstrassCurve.Affine

variable {C : Curve} [Fact C.p.Prime]

/-- A point as `O`, or its `x` and the half its `y` is in. -/
noncomputable def enc : (wcC C).Point → Option (ZMod C.p × Bool)
  | .zero => none
  | .some x y _ => some (x, decide (y.val ≤ C.p / 2))

theorem y_sq {x y : ZMod C.p} (h : (wcC C).Nonsingular x y) :
    y ^ 2 = x ^ 3 + (C.a : ZMod C.p) * x + (C.b : ZMod C.p) :=
  wc_equation.mp h.1

theorem enc_injective (hC : Good C) : Function.Injective (enc (C := C)) := by
  intro P Q h
  match P, Q with
  | .zero, .zero => rfl
  | .zero, .some .. => simp [enc] at h
  | .some .., .zero => simp [enc] at h
  | .some x₁ y₁ h₁, .some x₂ y₂ h₂ =>
    simp only [enc, Option.some.injEq, Prod.mk.injEq, decide_eq_decide] at h
    obtain ⟨rfl, hh⟩ := h
    have e : (y₁ - y₂) * (y₁ + y₂) = 0 := by
      have := y_sq h₁; have := y_sq h₂; linear_combination y_sq h₁ - y_sq h₂
    rcases mul_eq_zero.mp e with e | e
    · exact some_eq rfl (sub_eq_zero.mp e)
    · by_cases hy : y₁ = 0
      · have : y₂ = 0 := by rw [hy] at e; simpa using e
        exact some_eq rfl (by rw [hy, this])
      · exfalso
        have hy₂ : y₂ = -y₁ := by linear_combination e
        have hp := (Fact.out : C.p.Prime)
        have hodd : C.p % 2 = 1 := by
          rcases hp.eq_two_or_odd with h | h
          · have := hC.two_lt; omega
          · exact h
        have hv : y₂.val = C.p - y₁.val := by
          simp only [hy₂, ZMod.neg_val, hy, ↓reduceIte]
        have hpos : 0 < y₁.val := by
          rcases Nat.eq_zero_or_pos y₁.val with h | h
          · exact absurd ((ZMod.val_eq_zero y₁).mp h) hy
          · exact h
        have hlt : y₁.val < C.p := ZMod.val_lt y₁
        rw [hv] at hh
        have := hh
        omega

theorem card_le (hC : Good C) : Nat.card (wcC C).Point ≤ 2 * C.p + 1 := by
  have : NeZero C.p := ⟨(Fact.out : C.p.Prime).ne_zero⟩
  have := Nat.card_le_card_of_injective _ (enc_injective hC)
  rw [Nat.card_eq_fintype_card (α := Option _), Fintype.card_option, Fintype.card_prod,
    ZMod.card, Fintype.card_bool] at this
  omega

theorem finite_point (hC : Good C) : Finite (wcC C).Point :=
  Finite.of_injective _ (enc_injective hC)

/-- A point of order 2 has `y = 0`, a root of `x³ + ax + b`. -/
theorem no_two_torsion (hC : Good C) {Q : (wcC C).Point} (hQ : Q ≠ 0) : 2 • Q ≠ 0 := by
  intro h2
  have hneg : -Q = Q := by
    rw [two_nsmul] at h2
    exact (neg_eq_of_add_eq_zero_left h2)
  match Q, hQ with
  | .some x y hs, _ =>
    rw [Point.neg_some] at hneg
    have hy : (wcC C).negY x y = y := (Point.some.inj hneg).2
    rw [negY_wcC] at hy
    have h2y : (2 : ZMod C.p) * y = 0 := by linear_combination -hy
    rcases mul_eq_zero.mp h2y with h | h
    · exact two_ne_zero' hC.two_lt h
    · have := y_sq hs
      rw [h] at this
      exact hC.noTwoTorsion x (by linear_combination -this)

/-- The curve has `n` points. -/
theorem card_eq (hC : Good C) (hn : C.n.Prime) (hG : onCurve C (G C) = true)
    (hG0 : G C ≠ .infinity) (hnG : mul C.n (G C) = .infinity) (hb : 2 * C.p + 1 < 3 * C.n) :
    Nat.card (wcC C).Point = C.n := by
  haveI := finite_point hC
  haveI : Fact C.n.Prime := ⟨hn⟩
  have hGW : toW hC (G C) ≠ 0 := fun h => hG0 (toW_inj hC hG rfl (by rw [h]; rfl))
  have hnW : C.n • toW hC (G C) = 0 := by rw [← toW_mul hC hG, hnG]; rfl
  have hord : addOrderOf (toW hC (G C)) = C.n := addOrderOf_eq_prime hnW hGW
  have hdvd : C.n ∣ Nat.card (wcC C).Point := hord ▸ addOrderOf_dvd_natCard _
  have hle := card_le hC
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Nat.mul_zero] at hk
    exact Nat.card_pos.ne' hk
  have hk2 : k < 3 := by
    by_contra h
    have : C.n * 3 ≤ C.n * k := Nat.mul_le_mul_left _ (by omega)
    omega
  rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
  · rw [hk, Nat.mul_one]
  · exfalso
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨Q, hQ⟩ := exists_prime_addOrderOf_dvd_card' (G := (wcC C).Point) 2
      (by rw [hk]; exact Dvd.intro_left _ rfl)
    have hQ0 : Q ≠ 0 := by
      intro h; rw [h, addOrderOf_zero] at hQ; omega
    exact no_two_torsion hC hQ0 (by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q)

/-- `[n]P = O` for every point `P` of the curve. -/
theorem Good.mul_n (hC : Good C) (hn : C.n.Prime) (hG : onCurve C (G C) = true)
    (hG0 : G C ≠ .infinity) (hnG : mul C.n (G C) = .infinity) (hb : 2 * C.p + 1 < 3 * C.n)
    {P : Point C} (hP : onCurve C P = true) : mul C.n P = .infinity := by
  haveI := finite_point hC
  have hc := card_eq hC hn hG hG0 hnG hb
  have h : C.n • toW hC P = 0 := by rw [← hc]; exact card_nsmul_eq_zero'
  exact toW_inj hC (hC.onCurve_mul hP _) rfl (by rw [toW_mul hC hP, h]; rfl)

end VG.Proof.Weierstrass
