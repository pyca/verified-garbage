import VerifiedGarbage.Proof.Weierstrass.Complete
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The specification's group law is Mathlib's

On a curve with no point of order 2 (`Good`), every point of the curve is
nonsingular, and `toW` maps the specification's points to the points of
Mathlib's Weierstrass curve `y² = x³ + a x + b` over `ZMod p`: the
specification's addition is Mathlib's (`toW_add`), so its multiples are
Mathlib's (`toW_mul`), the reflection `(x, -y)` is the negation (`toW_neg`),
and `toW` is injective on the curve (`toW_inj`). Mathlib's points form an
abelian group, so the specification's points are one too (`Good.group`), and
with the rest of the group law's facts this is the interface the proofs of the
code take (`Good.law`), which only a curve's own facts import. The rest: the
ladder's loop over the scalar's bits and its iteration on projective
representatives, and the checks of a comb's tables without inverses.
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass WeierstrassCurve.Affine

variable {C : Curve}

/-! ## Scalar multiplication as a loop over the scalar's bits

The specification's `mul k P` recurses on `k / 2`; an implementation runs a
fixed number of iterations, one per bit of `k`, most significant first,
doubling an accumulator and adding `P` where the bit is set. After the bits
`t - 1, …, j` the accumulator is `mul (k >>> j) P` (`mul_shiftRight`), and
after all of them it is `mul k P` (`mul_eq_fold`). Multiples of a point of
the curve are on the curve (`onCurve_mul`).
-/

/-- One step of the loop: `(2m)P = mP + mP`, `(2m + 1)P = (mP + mP) + P`
(including `m = 0`, as `O + O = O`). -/
theorem mul_two_mul_add (P : Point C) (m : Nat) (bit : Bool) :
    mul (2 * m + bit.toNat) P =
      if bit then add (add (mul m P) (mul m P)) P else add (mul m P) (mul m P) := by
  by_cases h0 : 2 * m + bit.toNat = 0
  · have hm : m = 0 := by omega
    have hb : bit = false := by cases bit <;> simp_all
    subst hm hb
    rw [mul, ite_eq_left h0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [mul, ite_eq_left rfl]
    rfl
  · rw [mul, ite_eq_right h0]
    have hd : (2 * m + bit.toNat) / 2 = m := by
      cases bit <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
    have hr : (2 * m + bit.toNat) % 2 = bit.toNat := by cases bit <;> simp
    simp only [hd, hr]
    cases bit <;> simp

/-- The step on the scalar's bits: `k >>> j = 2 (k >>> (j + 1)) + bit j`. -/
theorem mul_shiftRight (P : Point C) (k j : Nat) :
    mul (k >>> j) P =
      if k.testBit j then add (add (mul (k >>> (j + 1)) P) (mul (k >>> (j + 1)) P)) P
      else add (mul (k >>> (j + 1)) P) (mul (k >>> (j + 1)) P) := by
  have hk : k >>> j = 2 * (k >>> (j + 1)) + (k.testBit j).toNat := by
    rw [Nat.testBit, Nat.shiftRight_succ, Nat.one_and_eq_mod_two]
    cases h : (k >>> j) % 2 == 1 <;> simp_all <;> omega
  rw [hk, mul_two_mul_add]

/-- The loop's body. -/
def ladderStep (k : Nat) (P R : Point C) (i : Nat) : Point C :=
  if k.testBit i then add (add R R) P else add R R

theorem foldl_ladderStep (P : Point C) (k j : Nat) :
    (List.range j).reverse.foldl (ladderStep k P) (mul (k >>> j) P) = mul k P := by
  induction j with
  | zero => rw [Nat.shiftRight_zero]; rfl
  | succ j ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons]
    rw [ladderStep, ← mul_shiftRight, ih]

/-- Scalar multiplication by a `t`-bit scalar, most significant bit first. -/
theorem mul_eq_fold (P : Point C) {k t : Nat} (hk : k < 2 ^ t) :
    mul k P = (List.range t).reverse.foldl
      (fun R i => if k.testBit i then add (add R R) P else add R R) .infinity := by
  have h0 : k >>> t = 0 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hk
  have := foldl_ladderStep P k t
  rw [h0, mul, ite_eq_left rfl] at this
  exact this.symm

/-- Multiples of a point of the curve are on the curve. -/
theorem onCurve_mul [Fact C.p.Prime] (hp : 2 < C.p) {P : Point C} (hP : onCurve C P = true)
    (k : Nat) : onCurve C (mul k P) = true := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    rw [mul]
    by_cases h0 : k = 0
    · rw [ite_eq_left h0]; rfl
    · rw [ite_eq_right h0]
      have hQ := ih (k / 2) (Nat.div_lt_self (by omega) (by decide))
      have h2 := onCurve_add hp hQ hQ
      dsimp only
      split
      · exact h2
      · exact onCurve_add hp h2 hP

theorem Good.onCurve_mul (hC : Good C) {P : Point C} (hP : onCurve C P = true) (k : Nat) :
    onCurve C (mul k P) = true := by
  have : Fact C.p.Prime := ⟨hC.prime⟩
  exact Weierstrass.onCurve_mul hC.two_lt hP k

/-! ## An iteration of the ladder on projective representatives

From a representative over `Fin p` of `[k >>> (j + 1)]P`, the complete
addition gives representatives of `D = R + R` and `T = D + P`, and selecting
`T` if bit `j` of `k` is set, else `D`, represents `[k >>> j]P`
(`Good.ladder_step`). With the rest of `Complete.lean` and `Group.lean`, this
makes the group law's interface for the proofs of the code (`Good.law`).
-/

theorem Good.ladder_step (hC : Good C) {P : Point C} (hP : onCurve C P = true) {k j : Nat}
    {Px Py Pz X Y Z X2 Y2 Z2 X3 Y3 Z3 : Fe C}
    (hPr : Rep C Px Py Pz P) (hR : Rep C X Y Z (mul (k >>> (j + 1)) P))
    (h2 : rcbAdd (Fin.ofNat C.p C.a) (Fin.ofNat C.p (3 * C.b)) X Y Z X Y Z = (X2, Y2, Z2))
    (h3 : rcbAdd (Fin.ofNat C.p C.a) (Fin.ofNat C.p (3 * C.b)) X2 Y2 Z2 Px Py Pz = (X3, Y3, Z3)) :
    Rep C (if k.testBit j then X3 else X2) (if k.testBit j then Y3 else Y2)
      (if k.testBit j then Z3 else Z2) (mul (k >>> j) P) := by
  have hm := hC.onCurve_mul hP (k >>> (j + 1))
  have hD := hC.rep_add hm hm hR hR h2
  have hDc := hC.onCurve_add hm hm
  have hT := hC.rep_add hDc hP hD hPr h3
  rw [mul_shiftRight P k j]
  by_cases hb : k.testBit j <;> simp only [hb, ite_true, ite_false, Bool.false_eq_true]
  · exact hT
  · exact hD

/-! ## The checks of a comb's tables

A chord or tangent checked without inverses (`chordOk`, `tangentOk`, which
`Law` states) is the specification's sum, by the slopes in `ZMod p`. -/

section
variable [Fact C.p.Prime]

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

end

section
variable [Fact C.p.Prime]

variable (C) in
/-- The curve over `ZMod p`, as Mathlib's Weierstrass curve. -/
abbrev wcC : WeierstrassCurve.Affine (ZMod C.p) :=
  wc (C.a : ZMod C.p) (C.b : ZMod C.p)

theorem equation_of_onCurve {x y : Fe C} (h : onCurve C (.affine x y) = true) :
    (wcC C).Equation (toF x) (toF y) :=
  wc_equation.mpr (onCurve_affine.mp h)

theorem negY_wcC (x y : ZMod C.p) : (wcC C).negY x y = -y := by
  simp [wcC, wc]

theorem y_ne_negY (hC : Good C) {x y : Fe C} (h : onCurve C (.affine x y) = true) :
    toF y ≠ (wcC C).negY (toF x) (toF y) := by
  rw [negY_wcC]
  intro h'
  have h2 : (2 : ZMod C.p) * toF y = 0 := by linear_combination h'
  rcases mul_eq_zero.mp h2 with h2 | h2
  · exact two_ne_zero' hC.two_lt h2
  · exact Weierstrass.y_ne_zero hC.noTwoTorsion (onCurve_affine.mp h) h2

theorem nonsingular_of_onCurve (hC : Good C) {x y : Fe C} (h : onCurve C (.affine x y) = true) :
    (wcC C).Nonsingular (toF x) (toF y) := by
  rw [nonsingular_iff']
  refine ⟨equation_of_onCurve h, Or.inr ?_⟩
  have := y_ne_negY hC h
  rw [negY_wcC] at this
  simp only [wcC, wc, zero_mul, add_zero]
  intro h2
  exact this (by linear_combination h2)

/-- A point of the specification as Mathlib's (`0` off the curve). -/
noncomputable def toW (hC : Good C) : Point C → (wcC C).Point
  | .infinity => 0
  | .affine x y =>
    if h : onCurve C (.affine x y) = true then .some (toF x) (toF y) (nonsingular_of_onCurve hC h)
    else 0

theorem toW_affine (hC : Good C) {x y : Fe C} (h : onCurve C (.affine x y) = true) :
    toW hC (.affine x y) = .some (toF x) (toF y) (nonsingular_of_onCurve hC h) := by
  rw [toW]
  simp only [h, ↓reduceDIte]

theorem some_eq {x₁ y₁ x₂ y₂ : ZMod C.p} {h₁ : (wcC C).Nonsingular x₁ y₁}
    {h₂ : (wcC C).Nonsingular x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : (wcC C).Point) = .some x₂ y₂ h₂ := by
  subst hx hy; rfl

/-- The specification's addition is Mathlib's. -/
theorem toW_add (hC : Good C) {P Q : Point C} (hP : onCurve C P = true)
    (hQ : onCurve C Q = true) : toW hC (add P Q) = toW hC P + toW hC Q := by
  match P, Q with
  | .infinity, Q => rw [toW, zero_add]; rfl
  | .affine x y, .infinity => rw [toW, add_zero]; rfl
  | .affine x₁ y₁, .affine x₂ y₂ =>
    have hS := hC.onCurve_add hP hQ
    rw [toW_affine hC hP, toW_affine hC hQ]
    by_cases hc : x₁ = x₂ ∧ y₂ = -y₁
    · obtain ⟨rfl, rfl⟩ := hc
      rw [add_neg, Point.add_of_Y_eq rfl (by rw [negY_wcC, toF_neg, neg_neg])]
      rfl
    by_cases hx : x₁ = x₂
    · subst hx
      obtain rfl : y₁ = y₂ := ((y_eq_or_eq_neg hP hQ).resolve_right (fun h => hc ⟨rfl, h⟩)).symm
      have hy : y₁ ≠ -y₁ := fun h => hc ⟨rfl, h⟩
      have hyW := y_ne_negY hC hP
      rw [Point.add_self_of_Y_ne hyW]
      have hl := toF_tangent_slope hC.two_lt (x₁ := x₁) (two_mul_ne_zero hy)
      have hsl : (wcC C).slope (toF x₁) (toF x₁) (toF y₁) (toF y₁) =
          toF ((3 * x₁ * x₁ + Fin.ofNat C.p C.a) * inv (2 * y₁)) := by
        rw [slope_of_Y_ne rfl hyW, negY_wcC, div_eq_iff (by
          rw [sub_neg_eq_add, ← two_mul]; exact two_mul_ne_zero hy)]
        simp only [wcC, wc]
        linear_combination -hl
      revert hS
      rw [add_tangent hy]
      intro hS
      rw [toW_affine hC hS]
      refine some_eq ?_ ?_
      · rw [addX, hsl]
        simp only [toF_sub, toF_mul, toF_ofNat' 2, wc]
        ring
      · rw [addY, negAddY, addX, hsl, negY_wcC]
        simp only [toF_sub, toF_mul, toF_ofNat' 2, wc]
        ring
    · have hl := toF_chord_slope hC.two_lt (y₁ := y₁) (y₂ := y₂) hx
      have hd : toF x₁ - toF x₂ ≠ 0 := fun h => hx (toF_injective (sub_eq_zero.mp h))
      have hsl : (wcC C).slope (toF x₁) (toF x₂) (toF y₁) (toF y₂) =
          toF ((y₂ - y₁) * inv (x₂ - x₁)) := by
        rw [slope_of_X_ne (fun h => hx (toF_injective h)), div_eq_iff hd]
        linear_combination hl
      revert hS
      rw [add_chord hx]
      intro hS
      rw [toW_affine hC hS, Point.add_of_X_ne (fun h => hx (toF_injective h))]
      refine some_eq ?_ ?_
      · rw [addX, hsl]
        simp only [toF_sub, toF_mul, wc]
        ring
      · rw [addY, negAddY, addX, hsl, negY_wcC]
        simp only [toF_sub, toF_mul, wc]
        ring

/-- The specification's multiples are Mathlib's. -/
theorem toW_mul (hC : Good C) {P : Point C} (hP : onCurve C P = true) :
    ∀ k, toW hC (mul k P) = k • toW hC P := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [mul]
    by_cases h0 : k = 0
    · simp only [h0, ↓reduceIte]; rw [zero_nsmul]; rfl
    simp only [h0, ↓reduceIte]
    have hm := hC.onCurve_mul hP (k / 2)
    have hd := hC.onCurve_add hm hm
    have IH := ih (k / 2) (by omega)
    split
    · rename_i h
      rw [toW_add hC hm hm, IH, ← add_smul]
      congr 1
      omega
    · rw [toW_add hC hd hP, toW_add hC hm hm, IH, ← add_smul, ← succ_nsmul]
      congr 1
      omega

/-- The reflection is the negation. -/
theorem toW_neg (hC : Good C) {P : Point C} (hP : onCurve C P = true) :
    toW hC (negPt P) = -toW hC P := by
  cases P with
  | infinity => rw [negPt, toW, neg_zero]
  | affine x y =>
    have hN : onCurve C (.affine x (-y)) = true := by
      rw [onCurve_affine, toF_neg] at *
      linear_combination hP
    rw [negPt, toW_affine hC hP, toW_affine hC hN, Point.neg_some]
    exact some_eq rfl (by rw [toF_neg, negY_wcC])

/-- `toW` is injective on the curve. -/
theorem toW_inj (hC : Good C) {P Q : Point C} (hP : onCurve C P = true)
    (hQ : onCurve C Q = true) (h : toW hC P = toW hC Q) : P = Q := by
  match P, Q with
  | .infinity, .infinity => rfl
  | .infinity, .affine x y =>
    rw [toW_affine hC hQ] at h; exact absurd h.symm (Point.some_ne_zero _)
  | .affine x y, .infinity =>
    rw [toW_affine hC hP] at h; exact absurd h (Point.some_ne_zero _)
  | .affine x₁ y₁, .affine x₂ y₂ =>
    rw [toW_affine hC hP, toW_affine hC hQ] at h
    obtain ⟨hx, hy⟩ := Point.some.inj h
    rw [toF_injective hx, toF_injective hy]

end

/-- On a curve the proofs apply to, the specification's group law is an
abelian group's. -/
theorem Good.group (hC : Good C) :
    ∃ (A : Type) (_ : Lean.Grind.IntModule A) (f : Point C → A), GroupRep C A f := by
  have : Fact C.p.Prime := ⟨hC.prime⟩
  refine ⟨_, inferInstance, toW hC, ⟨toW_add hC, fun hP k => ?_, toW_neg hC, toW_inj hC⟩⟩
  rw [toW_mul hC hP, ← natCast_zsmul]

theorem Good.mul_ne_zero (hC : Good C) {a b : Fe C} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  have : Fact C.p.Prime := ⟨hC.prime⟩
  intro h
  have h' : toF (a * b) = toF (0 : Fe C) := by rw [h]
  rw [toF_mul, toF_zero] at h'
  rcases _root_.mul_eq_zero.mp h' with h₀ | h₀
  · exact ha (toF_injective (h₀.trans toF_zero.symm))
  · exact hb (toF_injective (h₀.trans toF_zero.symm))

theorem Good.law (hC : Good C) : Law C where
  one_ne_zero := hC.one_ne_zero_fe
  mul_ne_zero := hC.mul_ne_zero
  add := hC.rep_add
  onCurve_add := hC.onCurve_add
  onCurve_mul := hC.onCurve_mul
  step := hC.ladder_step
  x_eq := hC.rep_x_eq
  y_eq := hC.rep_y_eq
  group := hC.group
  chord := fun h1 h2 hy1 h3 h => by
    have : Fact C.p.Prime := ⟨hC.prime⟩
    exact add_of_chordOk hC.two_lt h1 h2 hy1 h3 h
  tangent := fun h3 h => by
    have : Fact C.p.Prime := ⟨hC.prime⟩
    exact add_of_tangentOk hC.two_lt h3 h

end VG.Proof.Weierstrass
