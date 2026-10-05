import VerifiedGarbage.Proof.Ed25519.Group.Extended
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.PowLit

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.Edwards.URep`. -/
section

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

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.Edwards.Ladder`. -/
section

/-!
# X25519 of the base point is the u-coordinate of a multiple of Ed25519's

RFC 7748 §4.1's birational map `u = (1 + y) / (1 - y)` takes edwards25519's
base point `B` (Ed25519's, RFC 8032 §5.1) to curve25519's, `u = 9`:
`9 (1 - y_B) = 1 + y_B` (`base_u`). The ladder computes, after the bits
`254, …, n` of `k`, the u-coordinates of `[k >> n] B` and `[(k >> n) + 1] B`
(`inv_step`: `URep.dbl` and `URep.dadd`, whose difference is `B`), so
`X25519(k, 9)` is the u-coordinate `(1 + y) / (1 - y)` of `[k] B`
(`x25519_basePoint`), which a fixed-base multiplication on edwards25519 can
compute instead.

The field facts are evaluated by the kernel: `a24 = 121665` is
`-d / (1 + d)`, and `B`'s coordinates are those of RFC 8032.
-/

namespace VG.Proof.X25519.Edwards

open VG.Spec.X25519
open VG.Proof.Ed25519 (toZ_add toZ_sub toZ_mul toZ_one toZ_zero toZ_pow dZ baseAff params)
open VG.Proof.Ed25519.Edwards
open VG.Proof.X25519 (ladderAfter ladderAfter_step ladderAfter_255 ladderAfter_swap_le ladderStep_eq bit
  bit_le x25519_eq toFe leNum leNum_lt leNum_bit getD_set decodeLittleEndian_eq)

/-! ## The field facts -/

private theorem a24_fe : (1 + Spec.Ed25519.d) * a24 = 0 - Spec.Ed25519.d := by decide +kernel

/-- `(1 + d) a24 = -d`: `a24 = (A - 2) / 4` for `A = 2 (1 - d) / (1 + d)`. -/
theorem toZ_a24 : (1 + dZ) * Ed25519.toZ a24 = -dZ := by
  have e := congrArg Ed25519.toZ a24_fe
  rw [toZ_mul, toZ_add, toZ_one, toZ_sub, toZ_zero, zero_sub] at e
  exact e

/-! ## The base point -/

private theorem base_fe : (9 : Fe) * (1 - Spec.Ed25519.basePoint.Y) = 1 + Spec.Ed25519.basePoint.Y := by
  decide +kernel

/-- The base point's u-coordinate is 9. -/
theorem base_u : Ed25519.toZ 9 * (1 - baseAff.y) = 1 + baseAff.y := by
  have e := congrArg Ed25519.toZ base_fe
  rw [toZ_mul, toZ_sub, toZ_add, toZ_one] at e
  exact e

theorem base_x : baseAff.x ≠ 0 := by
  intro h
  have e : Spec.Ed25519.basePoint.X = 0 := Ed25519.toZ_inj.mp (h.trans toZ_zero.symm)
  exact absurd e (by decide +kernel)

theorem nine_ne : Ed25519.toZ 9 ≠ 0 := by
  intro h
  have e : (9 : Fe) = 0 := Ed25519.toZ_inj.mp (h.trans toZ_zero.symm)
  exact absurd e (by decide +kernel)

theorem u_basePoint : toFe (decodeUCoordinate basePoint) = 9 := by decide +kernel

/-! ## The ladder -/

/-- The u-coordinate `(X : Z)` of a pair of field elements is `p`'s. -/
abbrev U (a : Fe × Fe) (p : EPoint dZ) : Prop := URep (Ed25519.toZ a.1) (Ed25519.toZ a.2) p

/-- The ladder's state after the bits `254, …, n` of `k`: once swapped by
`swap`, the u-coordinates of `[k >> n] B` and `[(k >> n) + 1] B`. -/
def Inv (k n : Nat) (st : Ladder) : Prop :=
  U ((cswap st.swap st.x2 st.x3).1, (cswap st.swap st.z2 st.z3).1) ((k >>> n) • baseAff) ∧
    U ((cswap st.swap st.x2 st.x3).2, (cswap st.swap st.z2 st.z3).2) ((k >>> n + 1) • baseAff)

theorem dbl {x z : Fe} {p : EPoint dZ} (h : U (x, z) p) :
    U ((x + z) * (x + z) * ((x - z) * (x - z)),
      ((x + z) * (x + z) - (x - z) * (x - z)) *
        ((x + z) * (x + z) + a24 * ((x + z) * (x + z) - (x - z) * (x - z)))) (p + p) := by
  have := h.dbl toZ_a24
  simp only [U, toZ_mul, toZ_add, toZ_sub] at this ⊢
  exact this

theorem dadd {x2 z2 x3 z3 : Fe} {p q : EPoint dZ} (h2 : U (x2, z2) p) (h3 : U (x3, z3) q)
    (hb : q - p = baseAff ∨ p - q = baseAff) :
    U (((x3 - z3) * (x2 + z2) + (x3 + z3) * (x2 - z2)) * ((x3 - z3) * (x2 + z2) + (x3 + z3) * (x2 - z2)),
      9 * (((x3 - z3) * (x2 + z2) - (x3 + z3) * (x2 - z2)) *
        ((x3 - z3) * (x2 + z2) - (x3 + z3) * (x2 - z2)))) (p + q) := by
  have := h2.dadd h3 hb base_x base_u nine_ne
  simp only [U, toZ_mul, toZ_add, toZ_sub] at this ⊢
  exact this

/-- One iteration keeps `Inv`, for bit `n` of the scalar. -/
theorem inv_step (k n : Nat) (st : Ladder) (hs : st.swap ≤ 1) (h : Inv k (n + 1) st) :
    Inv k n (ladderStep k 9 st n) := by
  have hm : k >>> n = 2 * (k >>> (n + 1)) + bit k n := by
    simp only [bit, Nat.shiftRight_succ, Nat.and_one_is_mod]; omega
  set m := k >>> (n + 1)
  obtain ⟨h0, h1⟩ := h
  rw [ladderStep_eq]
  have hb := bit_le k n
  -- The swap applied in the step is the stored one, then the bit's.
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hs with hs0 | hs1 <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hb0 | hb1
  · simp only [hs0, hb0, cswap, Nat.xor_self, Nat.reduceEqDiff, ↓reduceIte] at h0 h1 ⊢
    refine ⟨?_, ?_⟩
    · rw [hm, hb0, Nat.add_zero, two_mul, add_nsmul]; exact dbl h0
    · rw [hm, hb0, Nat.add_zero, show 2 * m + 1 = m + (m + 1) by omega, add_nsmul]
      exact dadd h0 h1 (Or.inl (by rw [add_nsmul, one_nsmul, add_sub_cancel_left]))
  · simp only [hs0, hb1, cswap, Nat.zero_xor, ↓reduceIte] at h0 h1 ⊢
    refine ⟨?_, ?_⟩
    · rw [hm, hb1, show 2 * m + 1 = (m + 1) + m by omega, add_nsmul]
      exact dadd h1 h0 (Or.inr (by rw [add_nsmul, one_nsmul, add_sub_cancel_left]))
    · rw [hm, hb1, show 2 * m + 1 + 1 = (m + 1) + (m + 1) by omega, add_nsmul]; exact dbl h1
  · simp only [hs1, hb0, cswap, Nat.xor_zero, ↓reduceIte] at h0 h1 ⊢
    refine ⟨?_, ?_⟩
    · rw [hm, hb0, Nat.add_zero, two_mul, add_nsmul]; exact dbl h0
    · rw [hm, hb0, Nat.add_zero, show 2 * m + 1 = m + (m + 1) by omega, add_nsmul]
      exact dadd h0 h1 (Or.inl (by rw [add_nsmul, one_nsmul, add_sub_cancel_left]))
  · simp only [hs1, hb1, cswap, Nat.xor_self, ↓reduceIte] at h0 h1 ⊢
    refine ⟨?_, ?_⟩
    · rw [hm, hb1, show 2 * m + 1 = (m + 1) + m by omega, add_nsmul]
      exact dadd h1 h0 (Or.inr (by rw [add_nsmul, one_nsmul, add_sub_cancel_left]))
    · rw [hm, hb1, show 2 * m + 1 + 1 = (m + 1) + (m + 1) by omega, add_nsmul]; exact dbl h1

theorem inv_init (k : Nat) (h0 : k >>> 255 = 0) : Inv k 255 (VG.Proof.X25519.init 9) := by
  simp only [Inv, VG.Proof.X25519.init, cswap, h0, zero_nsmul, zero_add, one_nsmul, Nat.reduceEqDiff,
    ↓reduceIte]
  refine ⟨⟨?_, Or.inl ?_⟩, ⟨?_, Or.inr ?_⟩⟩
  · rw [toZ_one, toZ_zero, zero_y]; ring
  · rw [toZ_one]; exact one_ne_zero
  · rw [toZ_one, one_mul]; exact base_u
  · rw [toZ_one]; exact one_ne_zero

theorem inv_after (k : Nat) (hk : k >>> 255 = 0) :
    ∀ j ≤ 255, Inv k (255 - j) (ladderAfter k 9 (255 - j)) := by
  intro j
  induction j with
  | zero => intro _; rw [ladderAfter_255]; exact inv_init k hk
  | succ j ih =>
    intro hj
    have hn : 255 - (j + 1) < 255 := by omega
    rw [ladderAfter_step k 9 hn]
    have e : 255 - (j + 1) + 1 = 255 - j := by omega
    refine inv_step k _ _ ?_ ?_
    · rw [e]; exact ladderAfter_swap_le k 9 (by omega)
    · rw [e]; exact ih (by omega)

/-- Bit 7 of a byte masked with `127` and then 64 set is clear. -/
private theorem bit7_and_or_64 : ∀ x < 256, (((x &&& 127) ||| 64) >>> 7) &&& 1 = 0 := by
  decide +kernel

/-- The decoded scalar of 32 bytes has 255 bits (bit 255 is cleared). -/
theorem decodeScalar25519_shift {kb : List Byte} (h : kb.length = 32) :
    decodeScalar25519 kb >>> 255 = 0 := by
  have hlt : decodeScalar25519 kb < 2 ^ 256 := by
    simp only [decodeScalar25519, decodeLittleEndian_eq]
    refine Nat.lt_of_lt_of_le (leNum_lt _) ?_
    rw [show (2 : Nat) ^ 256 = 256 ^ 32 by norm_num]
    exact Nat.pow_le_pow_right (by decide) (List.length_take_le _ _)
  have hbit : (decodeScalar25519 kb >>> 255) &&& 1 = 0 := by
    simp only [decodeScalar25519, decodeLittleEndian_eq]
    rw [List.take_of_length_le (by simp [h]), leNum_bit,
      getD_set _ _ _ (by simp [h]), getD_set _ _ _ (by simp [h])]
    simp only [show 255 / 8 = 31 by rfl, show 255 % 8 = 7 by rfl, ↓reduceIte]
    rw [BitVec.toNat_or, BitVec.toNat_and, show (127 : BitVec 8).toNat = 127 from rfl,
      show (64 : BitVec 8).toNat = 64 from rfl]
    exact bit7_and_or_64 _ (BitVec.isLt _)
  have h2 : decodeScalar25519 kb >>> 255 < 2 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_succ]; exact hlt)
  rw [Nat.and_one_is_mod] at hbit
  omega

/-- `z^(P-2) = z⁻¹`, also for `z = 0`. -/
theorem pow_P_sub_two (z : ZMod P) : z ^ (P - 2) = z⁻¹ := by
  by_cases hz : z = 0
  · rw [hz, inv_zero, zero_pow (by decide +kernel)]
  · refine (eq_inv_of_mul_eq_one_left ?_)
    rw [← pow_succ, show P - 2 + 1 = P - 1 by decide +kernel, ZMod.pow_card_sub_one_eq_one hz]

/-- **X25519 of the base point** is the u-coordinate `(1 + y) / (1 - y)`
(with `(1 + y) / 0 = 0`) of `[k] B` on edwards25519, for the decoded scalar
`k` of a 32-byte string. -/
theorem x25519_basePoint {kb : List Byte} (hk : kb.length = 32) (w : Fe)
    (hw : Ed25519.toZ w = (1 + ((decodeScalar25519 kb) • baseAff).y) / (1 - ((decodeScalar25519 kb) • baseAff).y)) :
    x25519 kb basePoint = encodeUCoordinate w := by
  rw [x25519_eq, u_basePoint]
  simp only
  refine congrArg encodeUCoordinate (Ed25519.toZ_inj.mp ?_)
  have h := (inv_after (decodeScalar25519 kb) (decodeScalar25519_shift hk) 255 le_rfl).1
  rw [Nat.sub_self, Nat.shiftRight_zero] at h
  rw [hw, ← h.out params, toZ_mul, VG.Proof.X25519.invert_eq, toZ_pow, pow_P_sub_two]

end VG.Proof.X25519.Edwards

end
