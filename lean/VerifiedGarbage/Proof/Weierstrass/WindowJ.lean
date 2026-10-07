import VerifiedGarbage.Proof.Weierstrass.Window
import VerifiedGarbage.Proof.Weierstrass.Booth
import VerifiedGarbage.Proof.Weierstrass.JacAdd

/-!
# Signed windows in Jacobian coordinates, on any target

The window method of `Window.lean` with `R` in Jacobian coordinates and the
entries added by the Jacobian addition, which fails for equal or opposite
points. The table's entries are Jacobian triples whose projective
`(XZ : Y : Z³)` represents the point (`RepJ`), as `toJ` makes them of a
projective representative of a point other than `O` (`RepJ.of_toJ`).

When every point of the curve has order dividing `n`, a prime (`OrdN`), a
point `P ≠ O`'s integer multiples agree only for integers congruent modulo
`n` (`OrdN.zmul_eq`). Iteration `j` adds `[d_j]P` (`|d_j| ≤ 8`) to
`[16 e]P` with `e = winE k J (j + 1)`, so as long as `16 e + 8 < n` its
operands are neither equal nor opposite unless `[16 e]P = O` (`win_sep`); the
multiples `winE` only shrink as `j` grows (`winE_le_of_le`), so one bound
for `j = 1` serves every iteration but the last. The Jacobian sum then
represents the sum (`InvJ.sumSel`), taking `E` where `R` is `O` and `R`
where `E` is `O`.
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

variable {C : Curve}

/-! ## The table's representatives -/

/-- A Jacobian triple whose projective `(XZ : Y : Z³)` represents `Q`. -/
def RepJ (C : Curve) (X Y Z : Fe C) (Q : Point C) : Prop := Rep C (X * Z) Y (Z * Z * Z) Q

theorem RepJ.invJ {X Y Z : Fe C} {Q : Point C} (h : RepJ C X Y Z Q) : InvJ C X Y Z Q := Or.inr h

theorem RepJ.infinity (hC : Law C) : RepJ C 0 1 0 .infinity := by
  refine ⟨?_, hC.one_ne_zero, ?_⟩ <;> grind

theorem RepJ.negY {X Y Z : Fe C} {Q : Point C} (h : RepJ C X Y Z Q) : RepJ C X (-Y) Z (negPt Q) :=
  Rep.negY h

/-- `toJ` of a projective representative of a point other than `O`. -/
theorem RepJ.of_toJ (hC : Law C) {X Y Z z X' Y' Z' : Fe C} {Q : Point C} (h : Rep C X Y Z Q)
    (hQ : Q ≠ .infinity) (hz : z = 0) (hv : (X', Y', Z') = (X * Z, Y * (Z * Z), Z + z)) :
    RepJ C X' Y' Z' Q := by
  rcases InvJ.of_toJ hC h hz hv with ⟨h0, -⟩ | h'
  · exact absurd h0 hQ
  · exact h'

/-- `fromJ` of a representative: a projective representative. -/
theorem RepJ.fromJ {X Y Z z X' Y' Z' : Fe C} {Q : Point C} (h : RepJ C X Y Z Q) (hz : z = 0)
    (hv : (X', Y', Z') = (X * Z, Y + z, Z * Z * Z)) : Rep C X' Y' Z' Q := by
  simp only [Prod.mk.injEq] at hv
  obtain ⟨rfl, rfl, rfl⟩ := hv
  rw [hz, show Y + 0 = Y by grind]
  exact h

/-! ## Every point of order `n` -/

/-- Every point of the curve is killed by `n`, which is prime (as the
coprimality of the numbers below it). -/
structure OrdN (C : Curve) : Prop where
  pos : 0 < C.n
  cop : ∀ m, 0 < m → m < C.n → Nat.gcd m C.n = 1
  mul_n : ∀ {P : Point C}, onCurve C P = true → mul C.n P = .infinity

/-- Integer multiples of a point `P ≠ O` less than `n` apart agree only if
equal. -/
theorem OrdN.zmul_eq (hO : OrdN C) (hC : Law C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) {a b : Int} (hab : (a - b).natAbs < C.n) (h : zmul a P = zmul b P) :
    a = b := by
  have hd := hC.zmul_dvd_of hP hP0 (hO.mul_n hP) hO.pos hO.cop h
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast] at hd
  have := Nat.eq_zero_of_dvd_of_lt hd hab
  omega

theorem winPt_zmul (P : Point C) (k j : Nat) :
    winPt C P k j = zmul ((nib k j : Int) - 8) P := by
  unfold winPt zmul
  split
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]; congr 1; omega
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; congr 2; omega

/-- Iteration `j`'s operands, `[16 e]P` for `e = winE k J (j + 1)` and the
point of digit `j`, are neither equal nor opposite if `16 e + 8 < n` and
`[16 e]P ≠ O`. -/
theorem win_sep (hC : Law C) (hO : OrdN C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) {k J j : Nat} (hb : 16 * winE k J (j + 1) + 8 < C.n)
    (hR : mul (16 * winE k J (j + 1)) P ≠ .infinity) :
    mul (16 * winE k J (j + 1)) P ≠ winPt C P k j ∧
      Spec.Weierstrass.add (mul (16 * winE k J (j + 1)) P) (winPt C P k j) ≠ .infinity := by
  have hn := nib_lt k j
  generalize winE k J (j + 1) = e at hb hR
  have h0 : e ≠ 0 := by
    rintro rfl
    exact hR (by rw [Nat.mul_zero, Spec.Weierstrass.mul]; simp)
  rw [winPt_zmul, ← zmul_natCast]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := hO.zmul_eq hC hP hP0 (by omega) h
    omega
  · rw [hC.add_zmul hP, show (.infinity : Point C) = zmul 0 P by
      rw [zmul, ite_eq_left_of_eq_true _ _ (eq_true (Int.le_refl _))]; simp [Spec.Weierstrass.mul]] at h
    have := hO.zmul_eq hC hP hP0 (by omega) h
    omega

/-! ## The multiples shrink -/

theorem winE_succ_le {k J j : Nat} (hk : 8 * geom J ≤ k) (hj : j < J) :
    winE k J (j + 1) ≤ winE k J j := by
  have := winE_step hk hj
  have := nib_lt k j
  omega

theorem winE_le_of_le {k J : Nat} (hk : 8 * geom J ≤ k) {j : Nat} :
    ∀ {j'}, j ≤ j' → j' ≤ J → winE k J j' ≤ winE k J j
  | j', h, hJ => by
    rcases Nat.eq_or_lt_of_le h with rfl | h
    · exact Nat.le_refl _
    · obtain ⟨i, rfl⟩ : ∃ i, j' = i + 1 := ⟨j' - 1, by omega⟩
      exact Nat.le_trans (winE_succ_le hk (by omega)) (winE_le_of_le hk (by omega) (by omega))

/-- The multiples of a recoded scalar `d + 8 Σ_{i<J} 16^i`: `⌊(d + 8 Σ_{i<j} 16^i) / 16^j⌋`. -/
theorem winE_recode {d J j : Nat} (hj : j ≤ J) :
    winE (d + 8 * geom J) J j = (d + 8 * geom j) / 16 ^ j := by
  have hg := geom_add j (J - j)
  rw [Nat.add_sub_cancel' hj] at hg
  have hpos : 0 < 16 ^ j := Nat.pow_pos (by decide)
  have e : d + 8 * geom J = (d + 8 * geom j) + 16 ^ j * (8 * geom (J - j)) := by
    rw [hg]; grind
  rw [winE, e, Nat.add_mul_div_left _ _ hpos]
  exact Nat.add_sub_cancel _ _

/-- The bound `windowJ_ok` needs, for scalars below `2^b`. -/
theorem winE_two_bound {d J b n : Nat} (hJ : 2 ≤ J) (hd : d < 2 ^ b)
    (hb : 16 * ((2 ^ b + 135) / 256) + 8 < n) : 16 * winE (d + 8 * geom J) J 2 + 8 < n := by
  rw [winE_recode hJ]
  have : (d + 8 * geom 2) / 16 ^ 2 ≤ (2 ^ b + 135) / 256 :=
    Nat.div_le_div_right (show d + 8 * geom 2 ≤ 2 ^ b + 135 by
      show d + 8 * (0 + 1 + 16) ≤ _; omega)
  omega

/-! ## The Jacobian sum, selected -/

/-- Where neither is `O`, the Jacobian addition's `H` of points neither equal
nor opposite is not zero. -/
theorem InvJ.h_ne (hC : Law C) {X1 Y1 Z1 X2 Y2 Z2 : Fe C} {P Q : Point C}
    (hP : onCurve C P = true) (hQ : onCurve C Q = true)
    (h1 : InvJ C X1 Y1 Z1 P) (h2 : InvJ C X2 Y2 Z2 Q) (hz1 : Z1 ≠ 0) (hz2 : Z2 ≠ 0)
    (hne : P ≠ Q) (hadd : Spec.Weierstrass.add P Q ≠ .infinity) :
    X2 * (Z1 * Z1) - X1 * (Z2 * Z2) ≠ 0 := by
  intro hx
  by_cases hy : Y2 * Z1 * (Z1 * Z1) - Y1 * Z2 * (Z2 * Z2) = 0
  · exact hne (h1.same hC h2 hz1 hz2 hx hy)
  · exact hadd (h1.opposite hC hP hQ h2 hz1 hz2 hx hy)

/-- The sum `selSum` keeps: `E` where `Z₁ = 0`, `R` where `Z₂ = 0`, else the
Jacobian addition's, which represents the sum where its operands are neither
equal nor opposite. -/
theorem InvJ.sumSel (hC : Law C) (ha : AM3 C) {X1 Y1 Z1 X2 Y2 Z2 : Fe C} {P Q : Point C}
    (hP : onCurve C P = true) (hQ : onCurve C Q = true)
    (h1 : InvJ C X1 Y1 Z1 P) (h2 : InvJ C X2 Y2 Z2 Q)
    (hsep : P ≠ .infinity → Q ≠ .infinity → P ≠ Q ∧ Spec.Weierstrass.add P Q ≠ .infinity) :
    InvJ C (if Z1 = 0 then X2 else if Z2 = 0 then X1 else (jacAddF X1 Y1 Z1 X2 Y2 Z2).1)
      (if Z1 = 0 then Y2 else if Z2 = 0 then Y1 else (jacAddF X1 Y1 Z1 X2 Y2 Z2).2.1)
      (if Z1 = 0 then Z2 else if Z2 = 0 then Z1 else (jacAddF X1 Y1 Z1 X2 Y2 Z2).2.2)
      (Spec.Weierstrass.add P Q) := by
  by_cases hz1 : Z1 = 0
  · simp only [hz1, ↓reduceIte]
    rw [(h1.z_zero_iff hC).mp hz1]
    exact h2
  · by_cases hz2 : Z2 = 0
    · simp only [hz1, hz2, ↓reduceIte]
      rw [(h2.z_zero_iff hC).mp hz2]
      cases P <;> exact h1
    · simp only [hz1, hz2, ↓reduceIte]
      obtain ⟨hne, hadd⟩ := hsep (fun h => hz1 ((h1.z_zero_iff hC).mpr h))
        (fun h => hz2 ((h2.z_zero_iff hC).mpr h))
      exact h1.add_ne hC ha hP hQ h2 hz1 hz2 (h1.h_ne hC hP hQ h2 hz1 hz2 hne hadd)

end VG.Proof.Weierstrass
