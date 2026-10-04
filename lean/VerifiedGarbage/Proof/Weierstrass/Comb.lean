import VerifiedGarbage.Proof.Weierstrass.Law

/-!
# The fixed-base comb, on any target

For a scalar `k` and `J` digits `d_j = k_j - 8` of its nibbles `k_j`, the
comb's accumulator after the digits `J - 1` down to `j` is
`[combE k J j]G`, with `combE k J j = 8 Σ_{i<j} 16^i + Σ_{j≤i<J} k_i 16^i`
(`combE_step`): it starts at `[8 Σ_{i<J} 16^i]G` and ends at `[k]G`
(`combE_zero`, for `k < 16^J`). Adding `[d_j 16^j]G`, which is an entry of
table `j` or its reflection, takes `[combE k J (j+1)]G` to
`[combE k J j]G` (`comb_add`), by the group law (`Law.group`).

`CombOk` is what the code needs of its tables: entry `m` of table `j` is
`[(m + 1) 16^j]G`, and the start is `[8 Σ_{i<J} 16^i]G`, affine; a curve's
own facts prove it (`Proof/P256/Comb.lean`).
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

variable {C : Curve}

/-- `Σ_{i<j} 16^i`. -/
def geom : Nat → Nat
  | 0 => 0
  | j + 1 => geom j + 16 ^ j

/-- Nibble `j` of `k`. -/
def nib (k j : Nat) : Nat := k / 16 ^ j % 16

/-- The comb's multiple after the digits `J - 1` down to `j`. -/
def combE (k J j : Nat) : Nat := 8 * geom j + k % 16 ^ J / 16 ^ j * 16 ^ j

theorem nib_lt (k j : Nat) : nib k j < 16 := Nat.mod_lt _ (by decide)

theorem combE_top (k J : Nat) : combE k J J = 8 * geom J := by
  rw [combE, Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.pow_pos (by decide))), Nat.zero_mul, Nat.add_zero]

theorem combE_zero {k J : Nat} (hk : k < 16 ^ J) : combE k J 0 = k := by
  simp [combE, geom, Nat.mod_eq_of_lt hk]

/-- An iteration: `combE k J j + 8 16^j = combE k J (j+1) + k_j 16^j`. -/
theorem combE_step {k J j : Nat} (hj : j < J) :
    combE k J j + 8 * 16 ^ j = combE k J (j + 1) + nib k j * 16 ^ j := by
  have hq : k % 16 ^ J / 16 ^ j % 16 = nib k j := by
    have hdvd : 16 ^ j * 16 ∣ 16 ^ J := by
      rw [← Nat.pow_succ]; exact Nat.pow_dvd_pow 16 hj
    rw [← Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd k hdvd, Nat.mod_mul_right_div_self]
    rfl
  have hd : k % 16 ^ J / 16 ^ j = k % 16 ^ J / 16 ^ (j + 1) * 16 + nib k j := by
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← hq, Nat.div_add_mod']
  simp only [combE, geom]
  rw [hd, Nat.add_mul, Nat.pow_succ]
  have : k % 16 ^ J / (16 ^ j * 16) * 16 * 16 ^ j = k % 16 ^ J / (16 ^ j * 16) * (16 ^ j * 16) := by
    rw [Nat.mul_assoc, Nat.mul_comm 16 (16 ^ j)]
  omega

theorem eight_le_combE {k J j : Nat} : 8 * 16 ^ j ≤ combE k J (j + 1) := by
  simp only [combE, geom]; omega

/-! ## The group law, for the comb -/

theorem onCurve_negPt {P : Point C} (hP : onCurve C P = true) : onCurve C (negPt P) = true := by
  cases P with
  | infinity => rfl
  | affine x y =>
    simp only [negPt, onCurve, decide_eq_true_eq] at hP ⊢
    grind

theorem add_infinity (P : Point C) : Spec.Weierstrass.add P .infinity = P := by
  cases P <;> rfl

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

/-- What the comb needs of its tables for `G`: `J` tables of 8 entries, entry
`m` of table `j` the affine `[(m + 1) 16^j]G`, and the start the affine
`[8 Σ_{i<J} 16^i]G`, with coordinates below `p`. -/
structure CombOk (C : Curve) (J : Nat) (tbl : List (List (Nat × Nat))) (start : Nat × Nat) :
    Prop where
  len : tbl.length = J
  len8 : ∀ j < J, (tbl.getD j []).length = 8
  lt : ∀ j < J, ∀ m < 8, (combAt tbl j m).1 < C.p ∧ (combAt tbl j m).2 < C.p
  entry : ∀ j < J, ∀ m < 8, mul ((m + 1) * 16 ^ j) (G C) =
    .affine (Fin.ofNat C.p (combAt tbl j m).1) (Fin.ofNat C.p (combAt tbl j m).2)
  start_lt : start.1 < C.p ∧ start.2 < C.p
  start : mul (8 * geom J) (G C) = .affine (Fin.ofNat C.p start.1) (Fin.ofNat C.p start.2)

/-- The point of magnitude `a ≤ 8` in table `j`: `O` for `0`. -/
def combPt (C : Curve) (j a : Nat) : Point C := mul (a * 16 ^ j) (G C)

/-- An iteration's addition: `[combE k J (j+1)]G + [d_j 16^j]G = [combE k J j]G`,
with `[d_j 16^j]G` the point of magnitude `|d_j|`, reflected for `d_j < 0`. -/
theorem comb_add (hC : Law C) (hG : onCurve C (G C) = true) {k J j : Nat} (hj : j < J) :
    Spec.Weierstrass.add (mul (combE k J (j + 1)) (G C))
      (if 8 ≤ nib k j then combPt C j (nib k j - 8) else negPt (combPt C j (8 - nib k j))) =
      mul (combE k J j) (G C) := by
  have hs := combE_step (k := k) hj
  have h8 := eight_le_combE (k := k) (J := J) (j := j)
  split
  · rw [combPt, hC.add_mul_mul hG]
    congr 1
    rw [Nat.sub_mul]
    have : 8 * 16 ^ j ≤ nib k j * 16 ^ j := Nat.mul_le_mul_right _ ‹_›
    omega
  · rw [combPt, hC.add_mul_neg hG (by
      rw [Nat.sub_mul]; omega)]
    congr 1
    rw [Nat.sub_mul]
    have : nib k j * 16 ^ j ≤ 8 * 16 ^ j := Nat.mul_le_mul_right _ (by omega)
    omega

end VG.Proof.Weierstrass
