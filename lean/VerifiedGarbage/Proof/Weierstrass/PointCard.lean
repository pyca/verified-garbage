import VerifiedGarbage.Proof.Weierstrass.Group
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! A finite-field curve has at most two affine points for each x coordinate. -/
namespace VG.Proof.Weierstrass
open Spec.Weierstrass WeierstrassCurve.Affine

variable {C : Curve} [Fact C.p.Prime]

/-- The x coordinate and which of the two opposite y coordinates is smaller. -/
noncomputable def pointCode : (wcC C).Point → Option (ZMod C.p × Bool)
  | .zero => none
  | .some x y _ => some (x, decide (y.val ≤ (-y).val))

theorem pointCode_injective : Function.Injective (pointCode (C := C)) := by
  intro P Q h
  cases P with
  | zero => cases Q <;> simp_all [pointCode]
  | some x y hp =>
    cases Q with
    | zero => simp [pointCode] at h
    | some u v hq =>
      simp only [pointCode, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hx, hc⟩ := h
      rcases Point.X_eq_iff.mp hx with he | he
      · exact he
      · have hy : y = -v := by
          simp only [Point.neg_some, Point.some.injEq, negY_wcC] at he
          exact he.2
        subst y
        simp only [neg_neg, decide_eq_decide] at hc
        have hv : (-v).val = v.val := by omega
        have hv' : -v = v := ZMod.val_injective C.p hv
        exact some_eq hx hv'

instance finiteCurvePoints : Finite (wcC C).Point :=
  Finite.of_injective pointCode pointCode_injective

theorem card_points_le : Nat.card (wcC C).Point ≤ 2 * C.p + 1 := by
  let := Fintype.ofFinite (wcC C).Point
  have h := Fintype.card_le_of_injective pointCode (pointCode_injective (C := C))
  simpa only [Fintype.card_option, Fintype.card_prod, ZMod.card, Fintype.card_bool,
    Nat.card_eq_fintype_card, Nat.mul_comm] using h

theorem point_neg_fixed (hC : Good C) (P : (wcC C).Point) (h : -P = P) : P = 0 := by
  cases P with
  | zero => rfl
  | some x y hp =>
    have hy : -y = y := by
      simp only [Point.neg_some, Point.some.injEq, negY_wcC] at h
      exact h.2
    have h2 : (2 : ZMod C.p) * y = 0 := by linear_combination -hy
    have hz : y = 0 := (mul_eq_zero.mp h2).resolve_left (two_ne_zero' hC.two_lt)
    exact False.elim (y_ne_zero hC.noTwoTorsion (wc_equation.mp hp.1) hz)

/-- No nonzero point of order two implies the finite group has odd cardinality. -/
theorem two_not_dvd_card_points (hC : Good C) : ¬ 2 ∣ Nat.card (wcC C).Point := by
  intro h
  obtain ⟨P, hP⟩ := exists_prime_addOrderOf_dvd_card' 2 h
  have hzero : P + P = 0 := by
    rw [← two_nsmul, ← hP]
    exact addOrderOf_nsmul_eq_zero P
  have hP0 := point_neg_fixed hC P (neg_eq_iff_add_eq_zero.mpr hzero)
  simp only [hP0, addOrderOf_zero] at hP
  contradiction

end VG.Proof.Weierstrass
