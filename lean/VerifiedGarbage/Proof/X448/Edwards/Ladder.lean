import VerifiedGarbage.Proof.Edwards.Group
import VerifiedGarbage.Proof.Ed448.Group.Projective
import VerifiedGarbage.Proof.X448.Encoding
import VerifiedGarbage.Proof.Framework.PowLit

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Edwards.URep`. -/
section

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

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Edwards.Ladder`. -/
section

/-!
# X448 of the base point is the u-coordinate of a multiple of Ed448's

RFC 7748 §4.2's 4-isogeny `u = y² / x²` takes edwards448's base point `B`
(Ed448's, RFC 8032 §5.2) to curve448's, `u = 5`: `5 x_B² = y_B²` (`base_u`).
The ladder computes, after the bits `447, …, n` of `k`, the u-coordinates of
`[k >> n] B` and `[(k >> n) + 1] B` (`inv_step`: `URep.dbl` and `URep.dadd`,
whose difference is `B`), so `X448(k, 5)` is the u-coordinate `y² / x²` of
`[k] B` (`x448_basePoint`), which a fixed-base multiplication on edwards448
can compute instead.

The field facts are evaluated by the kernel: `1 - d = 39082` is not a square
(its power `(P - 1) / 2` is `-1`, as for `d` in `Ed448/Group/Projective.lean`),
and `a24 = -d`.
-/

namespace VG.Proof.X448.Edwards

open VG.Spec.X448
open VG.Proof.Ed448 (toZ_add toZ_sub toZ_mul toZ_one toZ_zero toZ_inj toZ_ne_zero toZ_pow toZ_neg
  dZ baseAff PZ PZ_eq pow_P_sub_one two_ne_zero')
open VG.Proof.EdwardsLaw
open VG.Proof.X448 (ladderAfter ladderAfter_step ladderAfter_448 ladderAfter_swap_le ladderStep_eq bit
  bit_le x448_eq toFe)

/-! ## The field facts -/

private theorem one_sub_d_pow : 39082 ^ ((P - 1) / 2) % PZ = PZ - 1 := by
  rw [← Pratt.powMod_eq PZ (by decide +kernel) 449 _ _ (by decide +kernel)]; decide +kernel

theorem one_sub_dZ : (1 : ZMod PZ) - dZ = ((39082 : Nat) : ZMod PZ) := by
  rw [dZ, show Spec.Ed448.d = 0 - 39081 from rfl, toZ_neg, sub_neg_eq_add]
  rw [show (39081 : Fe) = toFe 39081 from rfl]
  unfold Ed448.toZ toFe
  rw [Fin.val_ofNat, Nat.mod_eq_of_lt (by decide +kernel)]
  push_cast; ring

theorem one_sub_dZ_pow : (1 - dZ) ^ ((P - 1) / 2) = -1 := by
  rw [one_sub_dZ, ← Nat.cast_pow, ← ZMod.natCast_mod, one_sub_d_pow,
    Nat.cast_sub (by decide +kernel), ZMod.natCast_self, Nat.cast_one, zero_sub]

/-- `1 - d` is not a square in `ZMod PZ`. -/
theorem one_sub_dZ_nonsq (r : ZMod PZ) : r ^ 2 ≠ 1 - dZ := by
  intro hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    have h := one_sub_dZ_pow
    rw [← hr, zero_pow (by decide), zero_pow (by decide +kernel)] at h
    exact one_ne_zero (neg_eq_zero.mp h.symm)
  have h2 := one_sub_dZ_pow
  rw [← hr, ← pow_mul, show 2 * ((P - 1) / 2) = P - 1 by decide +kernel, pow_P_sub_one hr0] at h2
  exact two_ne_zero' (by linear_combination h2)

theorem toZ_a24 : Ed448.toZ a24 = -dZ := by
  rw [dZ, show Spec.Ed448.d = 0 - a24 from rfl, toZ_neg, neg_neg]

/-! ## The base point -/

private theorem base_fe : (5 : Fe) * (Spec.Ed448.basePoint.X * Spec.Ed448.basePoint.X) =
    Spec.Ed448.basePoint.Y * Spec.Ed448.basePoint.Y := by decide +kernel

/-- The base point's u-coordinate is 5. -/
theorem base_u : Ed448.toZ 5 * baseAff.x ^ 2 = baseAff.y ^ 2 := by
  have e := congrArg Ed448.toZ base_fe
  simp only [toZ_mul] at e
  simp only [baseAff, sq]
  exact e

theorem base_x : baseAff.x ≠ 0 :=
  toZ_ne_zero.mpr (by decide +kernel)

theorem five_ne : Ed448.toZ 5 ≠ 0 :=
  toZ_ne_zero.mpr (by decide +kernel)

theorem u_basePoint : toFe (decodeUCoordinate basePoint) = 5 := by decide +kernel

/-! ## The ladder -/

/-- The u-coordinate `(X : Z)` of a pair of field elements is `p`'s. -/
abbrev U (a : Fe × Fe) (p : EPoint dZ) : Prop := URep (Ed448.toZ a.1) (Ed448.toZ a.2) p

/-- The ladder's state after the bits `447, …, n` of `k`: once swapped by
`swap`, the u-coordinates of `[k >> n] B` and `[(k >> n) + 1] B`. -/
def Inv (k n : Nat) (st : Ladder) : Prop :=
  U ((cswap st.swap st.x2 st.x3).1, (cswap st.swap st.z2 st.z3).1) ((k >>> n) • baseAff) ∧
    U ((cswap st.swap st.x2 st.x3).2, (cswap st.swap st.z2 st.z3).2) ((k >>> n + 1) • baseAff)

theorem dbl {x z : Fe} {p : EPoint dZ} (h : U (x, z) p) :
    U ((x + z) * (x + z) * ((x - z) * (x - z)),
      ((x + z) * (x + z) - (x - z) * (x - z)) *
        ((x + z) * (x + z) + a24 * ((x + z) * (x + z) - (x - z) * (x - z)))) (p + p) := by
  have := h.dbl one_sub_dZ_nonsq
  simp only [U, toZ_mul, toZ_add, toZ_sub, toZ_a24] at this ⊢
  exact this

theorem dadd {x2 z2 x3 z3 : Fe} {p q : EPoint dZ} (h2 : U (x2, z2) p) (h3 : U (x3, z3) q)
    (hb : q - p = baseAff ∨ p - q = baseAff) :
    U (((x3 - z3) * (x2 + z2) + (x3 + z3) * (x2 - z2)) * ((x3 - z3) * (x2 + z2) + (x3 + z3) * (x2 - z2)),
      5 * (((x3 - z3) * (x2 + z2) - (x3 + z3) * (x2 - z2)) *
        ((x3 - z3) * (x2 + z2) - (x3 + z3) * (x2 - z2)))) (p + q) := by
  have := h2.dadd one_sub_dZ_nonsq h3 hb base_x base_u five_ne
  simp only [U, toZ_mul, toZ_add, toZ_sub] at this ⊢
  exact this

/-- One iteration keeps `Inv`, for bit `n` of the scalar. -/
theorem inv_step (k n : Nat) (st : Ladder) (hs : st.swap ≤ 1) (h : Inv k (n + 1) st) :
    Inv k n (ladderStep k 5 st n) := by
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

theorem inv_init (k : Nat) (h0 : k >>> 448 = 0) : Inv k 448 (VG.Proof.X448.init 5) := by
  simp only [Inv, VG.Proof.X448.init, cswap, h0, zero_nsmul, zero_add, one_nsmul, Nat.reduceEqDiff,
    ↓reduceIte]
  refine ⟨⟨?_, Or.inl ?_⟩, ⟨?_, Or.inr ?_⟩⟩
  · rw [toZ_one, toZ_zero, zero_x, zero_y]; ring
  · rw [toZ_one]; exact one_ne_zero
  · simp only [toZ_one, one_mul]; exact base_u
  · rw [toZ_one]; exact one_ne_zero

theorem inv_after (k : Nat) (hk : k >>> 448 = 0) :
    ∀ j ≤ 448, Inv k (448 - j) (ladderAfter k 5 (448 - j)) := by
  intro j
  induction j with
  | zero => intro _; rw [ladderAfter_448]; exact inv_init k hk
  | succ j ih =>
    intro hj
    have hn : 448 - (j + 1) < 448 := by omega
    rw [ladderAfter_step k 5 hn]
    have e : 448 - (j + 1) + 1 = 448 - j := by omega
    refine inv_step k _ _ ?_ ?_
    · rw [e]; exact ladderAfter_swap_le k 5 (by omega)
    · rw [e]; exact ih (by omega)

theorem shiftRight_of_lt {x n : Nat} (h : x < 256 ^ n) : x >>> (8 * n) = 0 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_mul]; exact Nat.div_eq_of_lt h

/-- The decoded scalar has 448 bits. -/
theorem decodeScalar448_shift (kb : List Byte) : decodeScalar448 kb >>> 448 = 0 := by
  rw [decodeScalar448, VG.Proof.X448.decodeLittleEndian_eq]
  exact shiftRight_of_lt (n := 56) (Nat.lt_of_lt_of_le (VG.Proof.X25519.leNum_lt _)
    (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _)))

/-- `z^(P-2) = z⁻¹`, also for `z = 0`. -/
theorem pow_P_sub_two (z : ZMod PZ) : z ^ (P - 2) = z⁻¹ := by
  by_cases hz : z = 0
  · rw [hz, inv_zero, zero_pow (by decide +kernel)]
  · refine (eq_inv_of_mul_eq_one_left ?_)
    rw [← pow_succ, show P - 2 + 1 = P - 1 by decide +kernel, pow_P_sub_one hz]

/-- **X448 of the base point** is the u-coordinate `y² / x²` (with `y² / 0 =
0`) of `[k] B` on edwards448, for the decoded scalar `k`. -/
theorem x448_basePoint (kb : List Byte) (w : Fe)
    (hw : Ed448.toZ w = ((decodeScalar448 kb) • baseAff).y ^ 2 / ((decodeScalar448 kb) • baseAff).x ^ 2) :
    x448 kb basePoint = encodeUCoordinate w := by
  rw [x448_eq, u_basePoint]
  simp only
  refine congrArg encodeUCoordinate (Ed448.toZ_inj.mp ?_)
  have h := (inv_after (decodeScalar448 kb) (decodeScalar448_shift kb) 448 le_rfl).1
  rw [Nat.sub_self, Nat.shiftRight_zero] at h
  rw [hw, ← h.out, toZ_mul, VG.Proof.X448.invert_eq, toZ_pow, pow_P_sub_two]

end VG.Proof.X448.Edwards

end
