import VerifiedGarbage.Proof.Weierstrass.WindowJ
import VerifiedGarbage.Proof.Weierstrass.JacMadd
import VerifiedGarbage.Proof.Weierstrass.JacAdd

/-!
# Signed windows in Jacobian coordinates with an affine table, on any target

The table's entries normalized to `Z = 1` by one inversion (Montgomery's
trick: the prefix products `c_m = Z_1 ⋯ Z_m`, `c_8^(p-2)`, then back from
`m = 8`: `Z_m^(p-2) = c_m^(p-2) c_{m-1}` and `c_{m-1}^(p-2) = c_m^(p-2) Z_m`),
which needs `Z Z^(p-2) = 1` for `Z ≠ 0` (`Law.fermat`, from `Law.x_eq`). The
entries are then representatives with `Z = 1`, or `(0 : 1 : 0)` for digit `0`
(`RepA`), and the iterations add them by the mixed addition (`maddJF`,
`InvJ.sumSelM`).
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

variable {C : Curve}

/-- Fermat's little theorem in `Fe C`: `1 = (1 Z) Z^(p-2)` (`Law.x_eq` for
the representative `(Z : 0 : Z)` of the pair `(1, 0)`). -/
theorem Law.fermat (hC : Law C) {Z : Fe C} (hZ : Z ≠ 0) : Z * Z ^ (C.p - 2) = 1 := by
  have h : Rep C (1 * Z) (0 * Z) Z (.affine 1 0) := ⟨hZ, rfl, rfl⟩
  have e := hC.x_eq h
  rw [e]; grind

theorem pow_mul_distrib (a b : Fe C) : ∀ k : Nat, (a * b) ^ k = a ^ k * b ^ k
  | 0 => by grind
  | k + 1 => by rw [Lean.Grind.Semiring.pow_succ, Lean.Grind.Semiring.pow_succ,
      Lean.Grind.Semiring.pow_succ, pow_mul_distrib a b k]; grind

/-- Back-substitution in Montgomery's trick: from `c^(p-2)` for `c = c' Z`,
`c' ≠ 0`: `Z^(p-2) = c^(p-2) c'` and `c'^(p-2) = c^(p-2) Z`. -/
theorem trick_step (hC : Law C) {c' Z : Fe C} (hc : c' ≠ 0) (hZ : Z ≠ 0) :
    (c' * Z) ^ (C.p - 2) * c' = Z ^ (C.p - 2) ∧ (c' * Z) ^ (C.p - 2) * Z = c' ^ (C.p - 2) := by
  rw [pow_mul_distrib]
  have h1 := hC.fermat hc
  have h2 := hC.fermat hZ
  constructor <;> grind

/-- A representative with `Z = 1` or `Z = 0`: the affine table's entries. -/
def RepA (C : Curve) (X Y Z : Fe C) (Q : Point C) : Prop := Rep C X Y Z Q ∧ (Z = 1 ∨ Z = 0)

theorem RepA.infinity (hC : Law C) : RepA C 0 1 0 .infinity := ⟨rep_infinity' hC, Or.inr rfl⟩

theorem RepA.negY {X Y Z : Fe C} {Q : Point C} (h : RepA C X Y Z Q) : RepA C X (-Y) Z (negPt Q) :=
  ⟨h.1.negY, h.2⟩

theorem RepA.invJ {X Y Z : Fe C} {Q : Point C} (h : RepA C X Y Z Q) : InvJ C X Y Z Q :=
  InvJ.of_rep01 h.1 h.2

/-- An affine point's coordinates by `Z^(p-2)`: a representative with `Z = 1`. -/
theorem RepA.of_rep (hC : Law C) {X Y Z : Fe C} {Q : Point C} (h : Rep C X Y Z Q)
    (hQ : Q ≠ .infinity) : RepA C (X * Z ^ (C.p - 2)) (Y * Z ^ (C.p - 2)) 1 Q := by
  cases Q with
  | infinity => exact absurd rfl hQ
  | affine x y =>
    rw [← hC.x_eq h, ← hC.y_eq h]
    exact ⟨⟨hC.one_ne_zero, (Lean.Grind.Semiring.mul_one _).symm, (Lean.Grind.Semiring.mul_one _).symm⟩,
      Or.inl rfl⟩

/-- The sum `selSum` keeps after the mixed addition: `E` where `Z₁ = 0`, `R`
where `Z₂ = 0`, else the mixed addition's, which represents the sum where the
operands are not equal. -/
theorem InvJ.sumSelM (hC : Law C) (ha : AM3 C) {X1 Y1 Z1 X2 Y2 Z2 : Fe C} {P Q : Point C}
    (hP : onCurve C P = true) (hQ : onCurve C Q = true)
    (h1 : InvJ C X1 Y1 Z1 P) (h2 : RepA C X2 Y2 Z2 Q)
    (hsep : P ≠ .infinity → Q ≠ .infinity → P ≠ Q) :
    InvJ C (if Z1 = 0 then X2 else if Z2 = 0 then X1 else (maddJF X1 Y1 Z1 X2 Y2).1)
      (if Z1 = 0 then Y2 else if Z2 = 0 then Y1 else (maddJF X1 Y1 Z1 X2 Y2).2.1)
      (if Z1 = 0 then Z2 else if Z2 = 0 then Z1 else (maddJF X1 Y1 Z1 X2 Y2).2.2)
      (Spec.Weierstrass.add P Q) := by
  by_cases hz1 : Z1 = 0
  · simp only [hz1, ↓reduceIte]
    rw [(h1.z_zero_iff hC).mp hz1]
    exact h2.invJ
  · by_cases hz2 : Z2 = 0
    · simp only [hz1, hz2, ↓reduceIte]
      have hQ0 : Q = .infinity := (h2.1.z_eq_zero_iff).mp hz2
      rw [hQ0]
      cases P <;> exact h1
    · simp only [hz1, hz2, ↓reduceIte]
      have hz2' : Z2 = 1 := h2.2.resolve_right hz2
      subst hz2'
      have hQa := h2.1.eq_affine hC
      subst hQa
      exact InvJ.madd hC ha hP hQ h1 hz1
        (hsep (fun h => hz1 ((h1.z_zero_iff hC).mpr h)) (fun h => nomatch h))

end VG.Proof.Weierstrass
