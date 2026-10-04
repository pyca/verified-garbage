import VerifiedGarbage.Proof.Edwards.Group

/-!
# The Montgomery ladder on the u-coordinates of Edwards points

Over any field with `2 ≠ 0` in which `d` and `1 - d` are not squares, the
map `(x, y) ↦ u = y² / x²` takes the Edwards curve `x² + y² = 1 + d x² y²` to
the Montgomery curve with `A = 2 - 4d` (RFC 7748 §4.2's 4-isogeny from
edwards448 to curve448, where `d = -39081` and `A = 156326`). `URep X Z p`:
the projective u-coordinate `(X : Z)` is `p`'s, `(y² : x²)`.

The ladder's two formulas (RFC 7748 §5, with `a24 = (A - 2) / 4 = -d`) act on
these as the group does:

* doubling takes `p`'s to `p + p`'s (`URep.dbl`);
* differential addition takes `p`'s and `q`'s to `p + q`'s, given the affine
  u-coordinate `u₁` of their difference `q - p` (or `p - q`): `URep.dadd`.

Neither formula ever gives `(0 : 0)`: `X + Z` and `X - Z` are `y² + x²` and
`y² - x²` scaled, and neither vanishes on the curve (`sum_ne`, `diff_ne`),
since `d` and `1 - d` are not squares. Hence `URep.out`: `X / Z = y² / x²`,
with `y² / 0 = 0` for the points with `x = 0`, whose u is infinite.
-/

namespace VG.Proof.X448.Edwards

open VG.Proof.EdwardsLaw

variable {F : Type*} [Field F] {d : F}

/-- `(X : Z)` is the projective u-coordinate `(y² : x²)` of `p`. -/
def URep (X Z : F) (p : EPoint d) : Prop := X * p.x ^ 2 = Z * p.y ^ 2 ∧ (X ≠ 0 ∨ Z ≠ 0)

/-- `y² + x² ≠ 0` on the curve: otherwise `d x⁴ = 1`, and `d = (1/x²)²`. -/
theorem sum_ne (hP : Params d) {x y : F} (h : OnCurve d x y) : y ^ 2 + x ^ 2 ≠ 0 := by
  intro hs
  unfold OnCurve at h
  have hd : d * x ^ 4 = 1 := by linear_combination h + (d * x ^ 2 - 1) * hs
  have hx : x ≠ 0 := by rintro rfl; simp at hd
  apply hP.nonsq (1 / x ^ 2)
  field_simp
  linear_combination -hd

/-- `y² - x² ≠ 0` on the curve if `1 - d` is not a square: otherwise
`(d x² - 1)² = 1 - d`. -/
theorem diff_ne (h1 : ∀ r : F, r ^ 2 ≠ 1 - d) {x y : F} (h : OnCurve d x y) : y ^ 2 - x ^ 2 ≠ 0 := by
  intro hs
  unfold OnCurve at h
  exact h1 (d * x ^ 2 - 1) (by linear_combination (-d) * h + (d - d ^ 2 * x ^ 2) * hs)

/-- A clearing step: `X (a/b)² = Z (c/e)²` from `X a² e² = Z c² b²`. -/
theorem cross {X Z a b c e : F} (hb : b ≠ 0) (he : e ≠ 0) (h : X * a ^ 2 * e ^ 2 = Z * c ^ 2 * b ^ 2) :
    X * (a / b) ^ 2 = Z * (c / e) ^ 2 := by
  field_simp
  linear_combination h

/-- The doubling identity, denominators cleared, for `(X : Z) = l (y² : x²)`. -/
theorem dbl_core {x y l : F} (h : OnCurve d x y) :
    let X := l * y ^ 2
    let Z := l * x ^ 2
    let AA := (X + Z) * (X + Z)
    let BB := (X - Z) * (X - Z)
    let E := AA - BB
    AA * BB * (x * y + y * x) ^ 2 * (1 - d * x * x * y * y) ^ 2 =
      E * (AA + -d * E) * (y * y - x * x) ^ 2 * (1 + d * x * x * y * y) ^ 2 := by
  intro X Z AA BB E
  unfold OnCurve at h
  simp only [X, Z, AA, BB, E]
  linear_combination
    (-16 * d * l ^ 4 * x ^ 4 * y ^ 4 * (x - y) ^ 2 * (x + y) ^ 2 * (d * x ^ 2 * y ^ 2 + x ^ 2 + y ^ 2 + 1)) * h

/-- The differential addition identity, denominators cleared, for
`(X₂ : Z₂) = l₂ (y₁² : x₁²)` and `(X₃ : Z₃) = l₃ (y₂² : x₂²)`, with the sum
and the difference of the points. -/
theorem dadd_core {x1 y1 x2 y2 l2 l3 : F} :
    let X2 := l2 * y1 ^ 2
    let Z2 := l2 * x1 ^ 2
    let X3 := l3 * y2 ^ 2
    let Z3 := l3 * x2 ^ 2
    let DA := (X3 - Z3) * (X2 + Z2)
    let CB := (X3 + Z3) * (X2 - Z2)
    (DA + CB) * (DA + CB) * (x1 * y2 + y1 * x2) ^ 2 * (x1 * y2 + y1 * -x2) ^ 2 =
      (DA - CB) * (DA - CB) * (y1 * y2 - x1 * x2) ^ 2 * (y1 * y2 - x1 * -x2) ^ 2 := by
  intro X2 Z2 X3 Z3 DA CB
  simp only [X2, Z2, X3, Z3, DA, CB]
  ring

/-- `(X : Z)` is `l (y² : x²)` for some `l ≠ 0`. -/
theorem URep.scale {X Z : F} {p : EPoint d} (h : URep X Z p) :
    ∃ l, l ≠ 0 ∧ X = l * p.y ^ 2 ∧ Z = l * p.x ^ 2 := by
  have hc := p.on
  unfold OnCurve at hc
  obtain ⟨he, hnz⟩ := h
  by_cases hx : p.x = 0
  · have hy : p.y ^ 2 = 1 := by rw [hx] at hc; linear_combination hc
    have hZ : Z = 0 := by rw [hx, hy] at he; linear_combination -he
    refine ⟨X, ?_, by rw [hy, mul_one], by rw [hZ, hx]; ring⟩
    rcases hnz with h | h
    · exact h
    · exact absurd hZ h
  · have hx2 : p.x ^ 2 ≠ 0 := pow_ne_zero 2 hx
    refine ⟨Z / p.x ^ 2, ?_, ?_, by field_simp⟩
    · intro h0
      have hZ : Z = 0 := (div_eq_zero_iff.mp h0).resolve_right hx2
      have hX : X = 0 := by
        rw [hZ, zero_mul] at he
        exact (mul_eq_zero.mp he).resolve_right hx2
      rcases hnz with h | h <;> contradiction
    · field_simp; linear_combination he

/-- Doubling (RFC 7748 §5, with `a24 = -d`) takes `p`'s u-coordinate to
`p + p`'s. -/
theorem URep.dbl [Fact (Params d)] (h1 : ∀ r : F, r ^ 2 ≠ 1 - d) {X Z : F} {p : EPoint d}
    (h : URep X Z p) :
    let AA := (X + Z) * (X + Z)
    let BB := (X - Z) * (X - Z)
    let E := AA - BB
    URep (AA * BB) (E * (AA + -d * E)) (p + p) := by
  intro AA BB E
  have hP : Params d := Fact.out
  obtain ⟨l, hl, hX, hZ⟩ := h.scale
  have hA : X + Z ≠ 0 := by
    rw [hX, hZ, ← mul_add]; exact mul_ne_zero hl (sum_ne hP p.on)
  have hB : X - Z ≠ 0 := by
    rw [hX, hZ, ← mul_sub]; exact mul_ne_zero hl (diff_ne h1 p.on)
  refine ⟨?_, Or.inl (mul_ne_zero (mul_ne_zero hA hA) (mul_ne_zero hB hB))⟩
  rw [add_x, add_y, addX, addY]
  refine cross (den_add_ne hP p.on p.on) (den_sub_ne hP p.on p.on) ?_
  simp only [AA, BB, E, hX, hZ]
  exact dbl_core p.on

/-- Differential addition (RFC 7748 §5) takes `p`'s and `q`'s u-coordinates
to `p + q`'s, given the affine u-coordinate `u₁ ≠ 0` of their difference
`b`. -/
theorem URep.dadd [Fact (Params d)] (h1 : ∀ r : F, r ^ 2 ≠ 1 - d) {X2 Z2 X3 Z3 u1 : F} {p q b : EPoint d}
    (h2 : URep X2 Z2 p) (h3 : URep X3 Z3 q) (hb : q - p = b ∨ p - q = b) (hbx : b.x ≠ 0)
    (hu : u1 * b.x ^ 2 = b.y ^ 2) (hu0 : u1 ≠ 0) :
    let DA := (X3 - Z3) * (X2 + Z2)
    let CB := (X3 + Z3) * (X2 - Z2)
    URep ((DA + CB) * (DA + CB)) (u1 * ((DA - CB) * (DA - CB))) (p + q) := by
  intro DA CB
  have hP : Params d := Fact.out
  obtain ⟨l2, hl2, hX2, hZ2⟩ := h2.scale
  obtain ⟨l3, hl3, hX3, hZ3⟩ := h3.scale
  have hA : X2 + Z2 ≠ 0 := by
    rw [hX2, hZ2, ← mul_add]; exact mul_ne_zero hl2 (sum_ne hP p.on)
  have hB : X2 - Z2 ≠ 0 := by
    rw [hX2, hZ2, ← mul_sub]; exact mul_ne_zero hl2 (diff_ne h1 p.on)
  have hC : X3 + Z3 ≠ 0 := by
    rw [hX3, hZ3, ← mul_add]; exact mul_ne_zero hl3 (sum_ne hP q.on)
  have hD : X3 - Z3 ≠ 0 := by
    rw [hX3, hZ3, ← mul_sub]; exact mul_ne_zero hl3 (diff_ne h1 q.on)
  have hDA : DA ≠ 0 := mul_ne_zero hD hA
  -- The difference, as `p + (-q)`, has the same squared coordinates as `b`.
  have hsq : b.x ^ 2 = (p + -q).x ^ 2 ∧ b.y ^ 2 = (p + -q).y ^ 2 := by
    rcases hb with hb | hb
    · rw [← hb, ← neg_sub, sub_eq_add_neg, neg_x, neg_y]; exact ⟨by ring, rfl⟩
    · rw [← hb, sub_eq_add_neg]; exact ⟨rfl, rfl⟩
  have hdp := den_add_ne hP p.on q.on
  have hdm := den_sub_ne hP p.on q.on
  have hrx : (p + -q).x ^ 2 ≠ 0 := by rw [← hsq.1]; exact pow_ne_zero 2 hbx
  constructor
  · -- Multiply by the difference's `x²`, which is not zero.
    apply mul_right_cancel₀ hrx
    have key : (DA + CB) * (DA + CB) * (p + q).x ^ 2 * (p + -q).x ^ 2 =
        (DA - CB) * (DA - CB) * (p + q).y ^ 2 * (p + -q).y ^ 2 := by
      simp only [add_x, add_y, neg_x, neg_y, addX, addY, div_pow]
      have hdp' : 1 + d * p.x * -q.x * p.y * q.y ≠ 0 := by
        rw [show 1 + d * p.x * -q.x * p.y * q.y = 1 - d * p.x * q.x * p.y * q.y by ring]; exact hdm
      have hdm' : 1 - d * p.x * -q.x * p.y * q.y ≠ 0 := by
        rw [show 1 - d * p.x * -q.x * p.y * q.y = 1 + d * p.x * q.x * p.y * q.y by ring]; exact hdp
      field_simp
      have := @dadd_core F _ p.x p.y q.x q.y l2 l3
      simp only [DA, CB, hX2, hZ2, hX3, hZ3]
      linear_combination
        (1 - d * p.x * q.x * p.y * q.y) ^ 2 * (1 + d * p.x * q.x * p.y * q.y) ^ 2 * this
    rw [← hsq.1, ← hsq.2, ← hu] at key
    rw [← hsq.1]
    linear_combination key
  · by_cases hs : DA + CB = 0
    · right
      refine mul_ne_zero hu0 (mul_self_ne_zero.mpr ?_)
      rw [show DA - CB = 2 * DA by linear_combination (-1 : F) * hs]
      exact mul_ne_zero hP.two hDA
    · exact Or.inl (mul_self_ne_zero.mpr hs)

/-- The u-coordinate `X / Z` (with `Z⁻¹ = 0` for `Z = 0`) is `y² / x²` (with
`y² / 0 = 0`). -/
theorem URep.out {X Z : F} {p : EPoint d} (h : URep X Z p) : X * Z⁻¹ = p.y ^ 2 / p.x ^ 2 := by
  obtain ⟨l, hl, hX, hZ⟩ := h.scale
  by_cases hx : p.x = 0
  · rw [hZ, hx]; simp
  · rw [hX, hZ]; field_simp

end VG.Proof.X448.Edwards
