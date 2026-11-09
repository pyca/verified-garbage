module
-- separate module: isolate the group-law proofs from byte-codec and ABI bridge changes.

public import Wychelean.DH.X25519.Basic
public import VerifiedGarbage.Proof.Framework.PowLit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Projective Montgomery coordinates for Wychelean's curve and twist -/

@[expose] public section

namespace VG.Proof.X25519.Montgomery

open WeierstrassCurve
open _root_.X25519 (BaseField Twist)

abbrev Point (d : BaseField) := (Twist d).toAffine.Point

/-- The projective coordinate is finite exactly when its denominator is nonzero.
The twist's Weierstrass x-coordinate is `d` times the Montgomery u-coordinate. -/
def Rep (d X Z : BaseField) : Point d → Prop
  | .zero => Z = 0 ∧ X ≠ 0
  | .some x _ _ => d * X = x * Z ∧ Z ≠ 0

theorem equation {d x y : BaseField} (h : (Twist d).toAffine.Nonsingular x y) :
    y ^ 2 = x ^ 3 + d * 486662 * x ^ 2 + d ^ 2 * x := by
  have e := (Affine.equation_iff' ..).mp h.1
  simpa only [Twist, zero_mul, zero_add, add_zero, sub_eq_zero] using e

theorem negY (d x y : BaseField) : (Twist d).toAffine.negY x y = -y := by
  simp only [Affine.negY, Twist, zero_mul, sub_zero]

theorem Rep.scale {d X Z c : BaseField} {P : Point d} (h : Rep d X Z P) (hc : c ≠ 0) :
    Rep d (c * X) (c * Z) P := by
  cases P with
  | zero => exact ⟨by rw [h.1, mul_zero], mul_ne_zero hc h.2⟩
  | some x y hp =>
    exact ⟨by calc
      d * (c * X) = c * (d * X) := by ring
      _ = c * (x * Z) := by rw [h.1]
      _ = x * (c * Z) := by ring, mul_ne_zero hc h.2⟩

theorem Rep.neg {d X Z : BaseField} {P : Point d} (h : Rep d X Z P) : Rep d X Z (-P) := by
  cases P with
  | zero => exact h
  | some x y hp => exact h

theorem Rep.out {d X Z : BaseField} {P : Point d} (hd : d ≠ 0) (h : Rep d X Z P) :
    X / Z = _root_.X25519.uCoord P / d := by
  cases P with
  | zero => simp only [Rep] at h; simp [h.1, _root_.X25519.uCoord]
  | some x y hp =>
    simp only [_root_.X25519.uCoord]
    apply (div_eq_div_iff h.2 hd).mpr
    simpa only [mul_comm] using h.1

/-- The two homogeneous coordinates of Montgomery doubling. -/
def doubleX (X Z : BaseField) := (X ^ 2 - Z ^ 2) ^ 2
def doubleZ (X Z : BaseField) := 4 * X * Z * (X ^ 2 + 486662 * X * Z + Z ^ 2)

/-- A finite point with zero y cannot have x² = d². -/
theorem torsion_numerator {d x y : BaseField} (hd : d ≠ 0)
    (hp : (Twist d).toAffine.Nonsingular x y) (hy : y = 0) : x ^ 2 - d ^ 2 ≠ 0 := by
  have he := equation hp
  rw [hy] at he
  intro hz
  have hx : x = d ∨ x = -d := by
    apply (sq_eq_sq_iff_eq_or_eq_neg).mp
    exact sub_eq_zero.mp hz
  rcases hx with hx | hx
  all_goals rw [hx] at he
  · have hn : (486664 : BaseField) ≠ 0 := by decide
    have h : (486664 : BaseField) * d ^ 3 = 0 := by linear_combination -he
    exact (mul_ne_zero hn (pow_ne_zero 3 hd)) h
  · have hn : (486660 : BaseField) ≠ 0 := by decide
    have h : (486660 : BaseField) * d ^ 3 = 0 := by linear_combination -he
    exact (mul_ne_zero hn (pow_ne_zero 3 hd)) h

/-- Doubling of a finite point, in normalized projective coordinates. -/
theorem double_finite {d x y : BaseField} (hd : d ≠ 0)
    (hp : (Twist d).toAffine.Nonsingular x y) :
    Rep d (doubleX (x / d) 1) (doubleZ (x / d) 1)
      (Affine.Point.some x y hp + Affine.Point.some x y hp) := by
  have he := equation hp
  by_cases hy : y = 0
  · rw [Affine.Point.add_self_of_Y_eq (by rw [negY, hy, neg_zero])]
    constructor
    · dsimp [doubleZ]
      field_simp
      rw [hy] at he
      linear_combination -4 * he
    · dsimp [doubleX]
      apply pow_ne_zero 2
      intro h
      have hn := torsion_numerator hd hp hy
      apply hn
      field_simp at h
      linear_combination h
  · have hneg : y ≠ (Twist d).toAffine.negY x y := by
      rw [negY]
      intro h
      have h2 : (2 : BaseField) * y = 0 := by linear_combination h
      exact (mul_ne_zero (by decide) hy) h2
    rw [Affine.Point.add_self_of_Y_ne hneg]
    constructor
    · dsimp [Rep, doubleX, doubleZ]
      rw [Affine.slope_of_Y_ne rfl hneg]
      simp only [Affine.negY, Twist, zero_mul, sub_zero, sub_neg_eq_add]
      have h2y : y + y ≠ 0 := by simpa only [← two_mul] using mul_ne_zero (by decide : (2 : BaseField) ≠ 0) hy
      have htwo : (2 : BaseField) ≠ 0 := by decide
      field_simp [show (1 : BaseField) + 1 = 2 by ring]
      have hfour : (4 : BaseField) ≠ 0 := by decide
      norm_num only at ⊢
      field_simp
      linear_combination (d ^ 2 + 2 * d * 486662 * x + 3 * x ^ 2) ^ 2 * he
    · dsimp [doubleZ]
      have hx : x ≠ 0 := by
        intro hx
        rw [hx] at he
        simp only [zero_pow (by decide : 3 ≠ 0), zero_pow (by decide : 2 ≠ 0),
          mul_zero, add_zero] at he
        exact (pow_ne_zero 2 hy) he
      have hr : x ^ 2 + d * 486662 * x + d ^ 2 ≠ 0 := by
        intro h
        have : y ^ 2 = 0 := by linear_combination he + x * h
        exact (pow_ne_zero 2 hy) this
      apply mul_ne_zero
      · exact mul_ne_zero (mul_ne_zero (by decide) (div_ne_zero hx hd)) one_ne_zero
      · intro h
        apply hr
        field_simp at h
        linear_combination h

/-- Doubling preserves the projective representation, including infinity. -/
theorem Rep.double {d X Z : BaseField} {P : Point d} (hd : d ≠ 0) (h : Rep d X Z P) :
    Rep d (doubleX X Z) (doubleZ X Z) (P + P) := by
  cases P with
  | zero =>
    rw [show (Affine.Point.zero : Point d) + .zero = .zero from zero_add _]
    exact ⟨by simp [doubleZ, h.1], by simpa [doubleX, h.1] using pow_ne_zero 4 h.2⟩
  | some x y hp =>
    have hX : X = Z * (x / d) := by
      rw [← mul_div_assoc]
      apply (eq_div_iff hd).mpr
      simpa only [mul_comm, mul_div_assoc] using h.1
    rw [hX]
    convert (double_finite hd hp).scale (pow_ne_zero 4 h.2) using 1 <;>
      dsimp [doubleX, doubleZ] <;> ring

/-- The homogeneous coordinates of differential addition. -/
def addX (X Z X' Z' : BaseField) := (X * X' - Z * Z') ^ 2
def addZ (u X Z X' Z' : BaseField) := u * (X * Z' - Z * X') ^ 2

/-- The product of the x-coordinates of the sum and difference, with
all secant denominators cleared. -/
theorem secant_product (d x y x' y' : BaseField)
    (h : y ^ 2 = x ^ 3 + d * 486662 * x ^ 2 + d ^ 2 * x)
    (h' : y' ^ 2 = x' ^ 3 + d * 486662 * x' ^ 2 + d ^ 2 * x') :
    ((y - y') ^ 2 - (x + x' + d * 486662) * (x - x') ^ 2) *
      ((y + y') ^ 2 - (x + x' + d * 486662) * (x - x') ^ 2) =
        (x * x' - d ^ 2) ^ 2 * (x - x') ^ 2 := by
  linear_combination
    (y ^ 2 + (x ^ 3 + d * 486662 * x ^ 2 + d ^ 2 * x) - 2 * y' ^ 2 -
      2 * (x + x' + d * 486662) * (x - x') ^ 2) * h +
    (y' ^ 2 + (x' ^ 3 + d * 486662 * x' ^ 2 + d ^ 2 * x') -
      2 * (x ^ 3 + d * 486662 * x ^ 2 + d ^ 2 * x) -
      2 * (x + x' + d * 486662) * (x - x') ^ 2) * h'

/-- Differential addition when the two finite x-coordinates differ. -/
theorem add_finite_distinct {d x y x' y' u : BaseField} (hd : d ≠ 0) (hu : u ≠ 0)
    (hp : (Twist d).toAffine.Nonsingular x y)
    (hq : (Twist d).toAffine.Nonsingular x' y') (hx : x ≠ x')
    (huv : Rep d u 1 (Affine.Point.some x' y' hq - Affine.Point.some x y hp)) :
    Rep d (addX (x / d) 1 (x' / d) 1) (addZ u (x / d) 1 (x' / d) 1)
      (Affine.Point.some x y hp + Affine.Point.some x' y' hq) := by
  have hden : x - x' ≠ 0 := sub_ne_zero.mpr hx
  have hden' : x' - x ≠ 0 := sub_ne_zero.mpr hx.symm
  rw [sub_eq_add_neg, Affine.Point.neg_some, Affine.Point.add_of_X_ne hx.symm] at huv
  have he : d * u = ((y' + y) / (x' - x)) ^ 2 - d * 486662 - x' - x := by
    have e := huv.1
    dsimp at e
    rw [Affine.slope_of_X_ne hx.symm] at e
    simpa only [Affine.negY, Twist, zero_mul, sub_zero, sub_neg_eq_add, add_zero, mul_one] using e
  rw [Affine.Point.add_of_X_ne hx]
  constructor
  · dsimp [Rep, addX, addZ]
    rw [Affine.slope_of_X_ne hx]
    simp only [Twist, zero_mul, add_zero]
    field_simp at he ⊢
    have hpq := secant_product d x y x' y' (equation hp) (equation hq)
    apply mul_right_cancel₀ (pow_ne_zero 2 hden)
    linear_combination -hpq -
      ((y - y') ^ 2 - (x + x' + d * 486662) * (x - x') ^ 2) * he
  · dsimp [addZ]
    apply mul_ne_zero hu
    apply pow_ne_zero 2
    simp only [mul_one, one_mul]
    exact sub_ne_zero.mpr (fun e => hx ((div_left_inj' hd).mp e))

theorem Rep.nonzero {d X Z : BaseField} {P : Point d} (h : Rep d X Z P) : X ≠ 0 ∨ Z ≠ 0 := by
  cases P with
  | zero => exact Or.inl h.2
  | some x y hp => exact Or.inr h.2

theorem Rep.cross {d X Z X' Z' : BaseField} {P : Point d} (hd : d ≠ 0)
    (h : Rep d X Z P) (h' : Rep d X' Z' P) : X * Z' = X' * Z := by
  cases P with
  | zero => simp only [h.1, h'.1, mul_zero]
  | some x y hp =>
    apply mul_left_cancel₀ hd
    linear_combination Z' * h.1 - Z * h'.1

/-- Differential addition at equal x-coordinates. The two points must be
opposites since their difference has a finite nonzero coordinate. -/
theorem add_finite_equal {d x y y' u : BaseField} (hd : d ≠ 0) (hu : u ≠ 0)
    (hp : (Twist d).toAffine.Nonsingular x y)
    (hq : (Twist d).toAffine.Nonsingular x y')
    (huv : Rep d u 1 (Affine.Point.some x y' hq - Affine.Point.some x y hp)) :
    Rep d (addX (x / d) 1 (x / d) 1) (addZ u (x / d) 1 (x / d) 1)
      (Affine.Point.some x y hp + Affine.Point.some x y' hq) := by
  rcases Affine.Point.X_eq_iff.mp (rfl : x = x) with heq | hneg
  · rw [heq, sub_self] at huv
    exact (one_ne_zero huv.1).elim
  · have hqneg : Affine.Point.some x y' hq = -Affine.Point.some x y hp := by
      exact hneg
    have hs : Affine.Point.some x y hp + Affine.Point.some x y' hq = 0 := by
      rw [hqneg, add_neg_cancel]
    have hdouble : Rep d u 1 (Affine.Point.some x y hp + Affine.Point.some x y hp) := by
      have hn := huv.neg
      rw [hqneg, sub_eq_add_neg, ← neg_add, neg_neg] at hn
      exact hn
    have hb := double_finite hd hp
    have he := hb.cross hd hdouble
    rw [hs]
    constructor
    · simp [addZ]
    · have he' : doubleX (x / d) 1 = u * doubleZ (x / d) 1 := by simpa only [mul_one] using he
      have hn : doubleX (x / d) 1 ≠ 0 := by
        intro hz
        have hz' : doubleZ (x / d) 1 = 0 := (mul_eq_zero.mp (he'.symm.trans hz)).resolve_left hu
        rcases hb.nonzero with h | h
        · exact h hz
        · exact h hz'
      simpa only [addX, doubleX, mul_one, one_pow, ← pow_two] using hn

theorem add_infinity_left {d X X' Z' u : BaseField} {Q : Point d}
    (hd : d ≠ 0) (hu : u ≠ 0) (hX : X ≠ 0) (hq : Rep d X' Z' Q)
    (huv : Rep d u 1 Q) :
    Rep d (addX X 0 X' Z') (addZ u X 0 X' Z') Q := by
  cases Q with
  | zero => exact (one_ne_zero huv.1).elim
  | some x y hp =>
    have he : X' = u * Z' := by
      apply mul_left_cancel₀ hd
      linear_combination hq.1 - Z' * huv.1
    constructor
    · dsimp [addX, addZ]
      rw [he]
      linear_combination X ^ 2 * u * Z' ^ 2 * huv.1
    · simpa only [addZ, zero_mul, sub_zero] using
        mul_ne_zero hu (pow_ne_zero 2 (mul_ne_zero hX hq.2))

/-- Differential addition preserves the projective representation. -/
theorem Rep.add {d X Z X' Z' u : BaseField} {P Q : Point d}
    (hd : d ≠ 0) (hu : u ≠ 0) (hp : Rep d X Z P) (hq : Rep d X' Z' Q)
    (huv : Rep d u 1 (Q - P)) :
    Rep d (addX X Z X' Z') (addZ u X Z X' Z') (P + Q) := by
  cases P with
  | zero =>
    rw [show (Affine.Point.zero : Point d) = 0 from rfl, zero_add]
    rw [show (Affine.Point.zero : Point d) = 0 from rfl, sub_zero] at huv
    rw [hp.1]
    exact add_infinity_left hd hu hp.2 hq huv
  | some x y hP =>
    cases Q with
    | zero =>
      rw [show (Affine.Point.zero : Point d) = 0 from rfl, add_zero]
      rw [show (Affine.Point.zero : Point d) = 0 from rfl, zero_sub] at huv
      have hn := huv.neg
      rw [neg_neg] at hn
      rw [hq.1]
      convert add_infinity_left hd hu hq.2 hp hn using 1 <;> dsimp [addX, addZ] <;> ring
    | some x' y' hQ =>
      have hX : X = Z * (x / d) := by
        rw [← mul_div_assoc]
        apply (eq_div_iff hd).mpr
        simpa only [mul_comm] using hp.1
      have hX' : X' = Z' * (x' / d) := by
        rw [← mul_div_assoc]
        apply (eq_div_iff hd).mpr
        simpa only [mul_comm] using hq.1
      have hn : Z ^ 2 * Z' ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero 2 hp.2) (pow_ne_zero 2 hq.2)
      have hnorm : Rep d (addX (x / d) 1 (x' / d) 1) (addZ u (x / d) 1 (x' / d) 1)
          (Affine.Point.some x y hP + Affine.Point.some x' y' hQ) := by
        by_cases hx : x = x'
        · subst x'
          exact add_finite_equal hd hu hP hQ huv
        · exact add_finite_distinct hd hu hP hQ hx huv
      rw [hX, hX']
      convert hnorm.scale hn using 1 <;> dsimp [addX, addZ] <;> ring

end VG.Proof.X25519.Montgomery
