module

public import VerifiedGarbage.Proof.Weierstrass.Law

/-!
# The fixed-base comb, on any target

What the comb's proofs on every target share: the sums `geom j = Σ_{i<j} 16^i`,
the nibbles `nib k j` of a scalar `k`, the group law's sums of multiples of a
point (`Law.add_mul_mul`, `Law.add_mul_neg`), and entry `m` of table `j`
(`combAt`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

variable {C : Curve}

/-- `Σ_{i<j} 16^i`. -/
def geom : Nat → Nat
  | 0 => 0
  | j + 1 => geom j + 16 ^ j

/-- Nibble `j` of `k`. -/
def nib (k j : Nat) : Nat := k / 16 ^ j % 16

theorem nib_lt (k j : Nat) : nib k j < 16 := Nat.mod_lt _ (by decide)

/-! ## The group law, for the comb -/

theorem onCurve_negPt {P : Point C} (hP : onCurve C P = true) : onCurve C (negPt P) = true := by
  cases P with
  | infinity => rfl
  | affine x y =>
    simp only [negPt, onCurve, decide_eq_true_eq] at hP ⊢
    grind

theorem add_infinity (P : Point C) : Spec.Weierstrass.add P .infinity = P := by
  cases P <;> rfl

/-- `[1]P = P`. -/
theorem mul_one_pt (P : Point C) : mul 1 P = P := by
  rw [Spec.Weierstrass.mul]
  simp only [Nat.one_ne_zero, ↓reduceIte, Nat.reduceDiv, Nat.reduceMod, Nat.one_ne_zero]
  rw [Spec.Weierstrass.mul]
  simp only [↓reduceIte]
  rfl

/-- `[a]P + [b]P = [a + b]P`. -/
theorem Law.add_mul_mul (hC : Law C) {P : Point C} (hP : onCurve C P = true) (a b : Nat) :
    Spec.Weierstrass.add (mul a P) (mul b P) = mul (a + b) P := by
  obtain ⟨A, _, f, hf⟩ := hC.group
  have ha := hC.onCurve_mul hP a
  have hb := hC.onCurve_mul hP b
  apply hf.inj (hC.onCurve_add ha hb) (hC.onCurve_mul hP _)
  rw [hf.add ha hb, hf.mul hP, hf.mul hP, hf.mul hP, Int.natCast_add,
    Lean.Grind.IntModule.add_zsmul]

/-- `[a]P - [b]P = [a - b]P` for `b ≤ a`. -/
theorem Law.add_mul_neg (hC : Law C) {P : Point C} (hP : onCurve C P = true) {a b : Nat}
    (hab : b ≤ a) : Spec.Weierstrass.add (mul a P) (negPt (mul b P)) = mul (a - b) P := by
  obtain ⟨A, _, f, hf⟩ := hC.group
  have ha := hC.onCurve_mul hP a
  have hb := hC.onCurve_mul hP b
  apply hf.inj (hC.onCurve_add ha (onCurve_negPt hb)) (hC.onCurve_mul hP _)
  rw [hf.add ha (onCurve_negPt hb), hf.neg hb, hf.mul hP, hf.mul hP, hf.mul hP]
  have e : ((a - b : Nat) : Int) = (a : Int) + (-(b : Int)) := by omega
  rw [e, Lean.Grind.IntModule.add_zsmul, Lean.Grind.IntModule.neg_zsmul]

/-! ## The tables -/

/-- Entry `m` of table `j`, `(0, 0)` past the end. -/
def combAt (tbl : List (List (Nat × Nat))) (j m : Nat) : Nat × Nat := (tbl.getD j []).getD m (0, 0)

end VG.Proof.Weierstrass
