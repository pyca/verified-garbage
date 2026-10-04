import VerifiedGarbage.Proof.Ed25519.Group.Extended

/-!
# The Montgomery ladder on the u-coordinates of twisted Edwards points

Over any field with `2 ≠ 0`, a square root of `-1` and a nonsquare `d`, the
map `(x, y) ↦ u = (1 + y) / (1 - y)` takes the twisted Edwards curve
`-x² + y² = 1 + d x² y²` to the Montgomery curve with `A = 2 (1 - d) / (1 + d)`
(RFC 7748 §4.1's birational map from edwards25519 to curve25519, where
`d = -121665 / 121666` and `A = 486662`). `URep X Z p`: the projective
u-coordinate `(X : Z)` is `p`'s, `(1 + y : 1 - y)`.

The ladder's two formulas (RFC 7748 §5, with `a24 = (A - 2) / 4`, that is
`(1 + d) a24 = -d`) act on these as the group does:

* doubling takes `p`'s to `p + p`'s (`URep.dbl`);
* differential addition takes `p`'s and `q`'s to `p + q`'s, given the affine
  u-coordinate `u₁` of their difference `q - p` (or `p - q`), if that
  difference has `x ≠ 0`: `URep.dadd`.

Neither formula gives `(0 : 0)` there. Hence `URep.out`: `X / Z = (1 + y) / (1 - y)`,
with `(1 + y) / 0 = 0` for the zero point, whose u is infinite.
-/

namespace VG.Proof.X25519.Edwards

open VG.Proof.Ed25519.Edwards

variable {F : Type*} [Field F] {d : F}

/-- `(X : Z)` is the projective u-coordinate `(1 + y : 1 - y)` of `p`. -/
def URep (X Z : F) (p : EPoint d) : Prop := X * (1 - p.y) = Z * (1 + p.y) ∧ (X ≠ 0 ∨ Z ≠ 0)

/-- `1 + d ≠ 0`: `-1` is a square and `d` is not. -/
theorem one_add_ne (hP : Params d) : 1 + d ≠ 0 := by
  intro h
  obtain ⟨s, hs⟩ := hP.sqrtm1
  exact hP.nonsq s (by linear_combination hs - h)

/-- `y = 1` only at `x = 0`. -/
theorem x_eq_zero_of_y (hP : Params d) {x y : F} (h : OnCurve d x y) (hy : y = 1) : x = 0 := by
  unfold OnCurve at h
  rw [hy] at h
  have : (1 + d) * x ^ 2 = 0 := by linear_combination -h
  exact pow_eq_zero_iff (n := 2) (by decide) |>.mp
    ((mul_eq_zero.mp this).resolve_left (one_add_ne hP))

/-- `(X : Z)` is `l (1 + y : 1 - y)` for some `l ≠ 0`. -/
theorem URep.scale (hP : Params d) {X Z : F} {p : EPoint d} (h : URep X Z p) :
    ∃ l, l ≠ 0 ∧ X = l * (1 + p.y) ∧ Z = l * (1 - p.y) := by
  obtain ⟨he, hnz⟩ := h
  by_cases hy : p.y = 1
  · have hZ : Z = 0 := by
      rw [hy] at he
      have : Z * 2 = 0 := by linear_combination -he
      exact (mul_eq_zero.mp this).resolve_right hP.two
    refine ⟨X / 2, ?_, ?_, ?_⟩
    · rcases hnz with h | h
      · exact div_ne_zero h hP.two
      · exact absurd hZ h
    · rw [hy, show (1 : F) + 1 = 2 by ring, div_mul_cancel₀ X hP.two]
    · rw [hy, hZ]; ring
  · have h1 : 1 - p.y ≠ 0 := fun h => hy (by linear_combination -h)
    refine ⟨Z / (1 - p.y), ?_, ?_, by field_simp⟩
    · intro h0
      have hZ : Z = 0 := (div_eq_zero_iff.mp h0).resolve_right h1
      have hX : X = 0 := by
        rw [hZ, zero_mul] at he
        exact (mul_eq_zero.mp he).resolve_right h1
      rcases hnz with h | h <;> contradiction
    · field_simp; linear_combination he

/-- The doubling identity, denominators cleared, for `(X : Z) = l (1 + y : 1 - y)`
and `(1 + d) a24 = -d`. -/
theorem dbl_core {x y l a24 : F} (h : OnCurve d x y) (ha : (1 + d) * a24 = -d) :
    let X := l * (1 + y)
    let Z := l * (1 - y)
    let AA := (X + Z) * (X + Z)
    let BB := (X - Z) * (X - Z)
    let E := AA - BB
    (1 + d) * (AA * BB * (1 - d * x * x * y * y - (y * y + x * x))) =
      (1 + d) * (E * (AA + a24 * E) * (1 - d * x * x * y * y + (y * y + x * x))) := by
  intro X Z AA BB E
  unfold OnCurve at h
  simp only [X, Z, AA, BB, E]
  linear_combination
    (16 * l ^ 4 * (d * y ^ 4 + 1)) * h -
      (4 * l ^ 2 * (1 - y ^ 2)) ^ 2 * (1 - d * x * x * y * y + (y * y + x * x)) * ha

/-- The differential addition identity, denominators cleared, for
`(X₂ : Z₂) = l₂ (1 + y₁ : 1 - y₁)` and `(X₃ : Z₃) = l₃ (1 + y₂ : 1 - y₂)`,
with the sum and the difference of the points. -/
theorem dadd_core {x1 y1 x2 y2 l2 l3 : F} (h1 : OnCurve d x1 y1) (h2 : OnCurve d x2 y2) :
    let X2 := l2 * (1 + y1)
    let Z2 := l2 * (1 - y1)
    let X3 := l3 * (1 + y2)
    let Z3 := l3 * (1 - y2)
    let DA := (X3 - Z3) * (X2 + Z2)
    let CB := (X3 + Z3) * (X2 - Z2)
    (DA + CB) * (DA + CB) * (1 - d * x1 * x2 * y1 * y2 - (y1 * y2 + x1 * x2)) *
        (1 + d * x1 * x2 * y1 * y2 - (y1 * y2 - x1 * x2)) =
      (DA - CB) * (DA - CB) * (1 - d * x1 * x2 * y1 * y2 + (y1 * y2 + x1 * x2)) *
        (1 + d * x1 * x2 * y1 * y2 + (y1 * y2 - x1 * x2)) := by
  intro X2 Z2 X3 Z3 DA CB
  unfold OnCurve at h1 h2
  simp only [X2, Z2, X3, Z3, DA, CB]
  linear_combination
    (64 * l2 ^ 2 * l3 ^ 2 * x2 ^ 2 * y1 * y2 * (d * y2 ^ 2 + 1)) * h1 +
      (64 * l2 ^ 2 * l3 ^ 2 * y1 * y2 * (y1 - 1) * (y1 + 1)) * h2

/-- Doubling (RFC 7748 §5) takes `p`'s u-coordinate to `p + p`'s. -/
theorem URep.dbl [hP : Fact (Params d)] {a24 X Z : F} (ha : (1 + d) * a24 = -d) {p : EPoint d}
    (h : URep X Z p) :
    let AA := (X + Z) * (X + Z)
    let BB := (X - Z) * (X - Z)
    let E := AA - BB
    URep (AA * BB) (E * (AA + a24 * E)) (p + p) := by
  intro AA BB E
  obtain ⟨l, hl, hX, hZ⟩ := h.scale hP.out
  have hd := den_sub_ne hP.out p.on p.on
  have h1d := one_add_ne hP.out
  have h2 : (2 : F) ≠ 0 := hP.out.two
  have h16 : (16 : F) ≠ 0 := by rw [show (16 : F) = 2 ^ 4 by norm_num]; exact pow_ne_zero 4 h2
  constructor
  · rw [add_y, addY]
    have key := dbl_core (l := l) p.on ha
    simp only at key
    have key' := mul_left_cancel₀ h1d key
    rw [one_sub_div hd, one_add_div hd, ← mul_div_assoc, ← mul_div_assoc, div_left_inj' hd]
    simp only [AA, BB, E, hX, hZ]
    linear_combination key'
  · -- `AA BB = 16 l⁴ y²`, and `E (AA + a24 E) = 16 l⁴ (1 - y²) (1 + d y²) / (1 + d)`.
    by_cases hy : p.y = 0
    · right
      have hE : E * (AA + a24 * E) * (1 + d) = 16 * l ^ 4 := by
        simp only [AA, BB, E, hX, hZ, hy]
        linear_combination (16 * l ^ 4) * ha
      intro h0
      rw [h0, zero_mul] at hE
      exact pow_ne_zero 4 hl ((mul_eq_zero.mp hE.symm).resolve_left h16)
    · left
      simp only [AA, BB, hX, hZ]
      have : (l * (1 + p.y) + l * (1 - p.y)) * (l * (1 + p.y) + l * (1 - p.y)) *
          ((l * (1 + p.y) - l * (1 - p.y)) * (l * (1 + p.y) - l * (1 - p.y))) =
          16 * (l ^ 4 * p.y ^ 2) := by ring
      rw [this]
      exact mul_ne_zero h16
        (mul_ne_zero (pow_ne_zero 4 hl) (pow_ne_zero 2 hy))

/-- Differential addition (RFC 7748 §5) takes `p`'s and `q`'s u-coordinates
to `p + q`'s, given the affine u-coordinate `u₁ ≠ 0` of their difference
`b`, if `b`'s `x` is not zero. -/
theorem URep.dadd [hP : Fact (Params d)] {X2 Z2 X3 Z3 u1 : F} {p q b : EPoint d}
    (h2 : URep X2 Z2 p) (h3 : URep X3 Z3 q) (hb : q - p = b ∨ p - q = b) (hbx : b.x ≠ 0)
    (hu : u1 * (1 - b.y) = 1 + b.y) (hu0 : u1 ≠ 0) :
    let DA := (X3 - Z3) * (X2 + Z2)
    let CB := (X3 + Z3) * (X2 - Z2)
    URep ((DA + CB) * (DA + CB)) (u1 * ((DA - CB) * (DA - CB))) (p + q) := by
  intro DA CB
  obtain ⟨l2, hl2, hX2, hZ2⟩ := h2.scale hP.out
  obtain ⟨l3, hl3, hX3, hZ3⟩ := h3.scale hP.out
  -- The difference, as `p + (-q)`, has `b`'s `y` and `x²`.
  have hsq : b.x ^ 2 = (p + -q).x ^ 2 ∧ b.y = (p + -q).y := by
    rcases hb with hb | hb
    · rw [← hb, ← neg_sub, sub_eq_add_neg, neg_x, neg_y]; exact ⟨by ring, rfl⟩
    · rw [← hb, sub_eq_add_neg]; exact ⟨rfl, rfl⟩
  have hdp := den_add_ne hP.out p.on q.on
  have hdm := den_sub_ne hP.out p.on q.on
  have hdp' : 1 + d * p.x * -q.x * p.y * q.y ≠ 0 := by
    rw [show 1 + d * p.x * -q.x * p.y * q.y = 1 - d * p.x * q.x * p.y * q.y by ring]; exact hdm
  have hdm' : 1 - d * p.x * -q.x * p.y * q.y ≠ 0 := by
    rw [show 1 - d * p.x * -q.x * p.y * q.y = 1 + d * p.x * q.x * p.y * q.y by ring]; exact hdp
  -- `1 - b.y ≠ 0`, since `b.x ≠ 0`.
  have hby : 1 - b.y ≠ 0 := fun h => hbx (x_eq_zero_of_y hP.out b.on (by linear_combination -h))
  constructor
  · apply mul_right_cancel₀ hby
    have key : (DA + CB) * (DA + CB) * (1 - (p + q).y) * (1 - (p + -q).y) =
        (DA - CB) * (DA - CB) * (1 + (p + q).y) * (1 + (p + -q).y) := by
      simp only [add_y, neg_x, neg_y, addY]
      rw [one_sub_div hdm, one_sub_div hdm', one_add_div hdm, one_add_div hdm']
      simp only [mul_div_assoc', div_mul_eq_mul_div, div_div]
      rw [div_left_inj' (mul_ne_zero hdm hdm')]
      have := dadd_core (l2 := l2) (l3 := l3) p.on q.on
      simp only at this
      simp only [DA, CB, hX2, hZ2, hX3, hZ3]
      linear_combination this
    rw [hsq.2] at hu ⊢
    linear_combination key - (DA - CB) * (DA - CB) * (1 + (p + q).y) * hu
  · -- `DA + CB = 4 l₂ l₃ (y₁ + y₂)` and `DA - CB = 4 l₂ l₃ (y₂ - y₁)`; both zero
    -- would make `y₁ = y₂ = 0`, and then the difference's `x` zero.
    have h2' : (2 : F) ≠ 0 := hP.out.two
    have hS : DA + CB = 4 * l2 * l3 * (p.y + q.y) := by simp only [DA, CB, hX2, hZ2, hX3, hZ3]; ring
    have hD : DA - CB = 4 * l2 * l3 * (q.y - p.y) := by simp only [DA, CB, hX2, hZ2, hX3, hZ3]; ring
    have h4 : 4 * l2 * l3 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2' h2') hl2) hl3
    by_cases hs : DA + CB = 0
    · right
      refine mul_ne_zero hu0 (mul_self_ne_zero.mpr ?_)
      intro hd
      rw [hS] at hs
      rw [hD] at hd
      have e1 := (mul_eq_zero.mp hs).resolve_left h4
      have e2 := (mul_eq_zero.mp hd).resolve_left h4
      have hpy : p.y = 0 := by
        have : 2 * p.y = 0 := by linear_combination e1 - e2
        exact (mul_eq_zero.mp this).resolve_left h2'
      have hqy : q.y = 0 := by linear_combination e1 - hpy
      apply hbx
      apply pow_eq_zero_iff (n := 2) (by decide) |>.mp
      rw [hsq.1, add_x, addX, neg_y, neg_x, hpy, hqy]
      simp
    · exact Or.inl (mul_self_ne_zero.mpr hs)

/-- The u-coordinate `X / Z` (with `Z⁻¹ = 0` for `Z = 0`) is `(1 + y) / (1 - y)`
(with `(1 + y) / 0 = 0`). -/
theorem URep.out (hP : Params d) {X Z : F} {p : EPoint d} (h : URep X Z p) :
    X * Z⁻¹ = (1 + p.y) / (1 - p.y) := by
  obtain ⟨l, hl, hX, hZ⟩ := h.scale hP
  by_cases hy : 1 - p.y = 0
  · rw [hZ, hy]; simp
  · rw [hX, hZ]; field_simp

end VG.Proof.X25519.Edwards
