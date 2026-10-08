import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.Weierstrass.JacMadd
import VerifiedGarbage.Proof.Weierstrass.JacAdd

/-! Architecture-independent masked Jacobian window arithmetic, including invalid scalars. -/
namespace VG.Proof.Weierstrass.Window5
open VG Spec.Weierstrass
variable {C : Curve}

/-- The iteration's result: `R` for a zero digit, else `T` where `R = O`, else
the Jacobian sum, a triple of `[winE k' J i]P`. -/
theorem jstep_point (hC : Law C) (hM3 : AM3 C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) (hn17 : C.n % 32 = 17) (hn64 : 64 ≤ C.n) {k J i : Nat} (hk : k < C.n)
    (hi : i < J) {X1 Y1 Z1 X2 Y2 Z2 : Fe C}
    (h1 : InvJ C X1 Y1 Z1 (mul (32 * Window5.winE (k + 16 * Window5.geom J) J (i + 1)) P))
    (h2 : 1 ≤ magH 16 (Window5.nib (k + 16 * Window5.geom J) i) →
      InvJ C X2 Y2 Z2 (Window5.winPt C P (k + 16 * Window5.geom J) i) ∧ Z2 ≠ 0) :
    InvJ C
      (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then X1
        else if Z1 = 0 then X2 else (jacAddF X1 Y1 Z1 X2 Y2 Z2).1)
      (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then Y1
        else if Z1 = 0 then Y2 else (jacAddF X1 Y1 Z1 X2 Y2 Z2).2.1)
      (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then Z1
        else if Z1 = 0 then Z2 else (jacAddF X1 Y1 Z1 X2 Y2 Z2).2.2)
      (mul (Window5.winE (k + 16 * Window5.geom J) J i) P) := by
  have hadd := Window5.win_add hC hP (k := k + 16 * Window5.geom J) (J := J) (j := i) (Nat.le_add_left _ _) hi
  generalize hk' : k + 16 * Window5.geom J = k' at hadd h1 h2 ⊢
  generalize he : Window5.winE k' J (i + 1) = e at hadd h1
  rw [← hadd]
  by_cases h0 : magH 16 (Window5.nib k' i) = 0
  · simp only [h0, ↓reduceIte]
    rw [Window5.winPt_zero h0, add_infinity]
    exact h1
  · simp only [h0, ↓reduceIte]
    obtain ⟨J2, z2⟩ := h2 (by omega)
    have hQ := hC.onCurve_mul hP (32 * e)
    have hW : onCurve C (Window5.winPt C P k' i) = true := Window5.onCurve_winPt hC hP k' i
    by_cases hz : Z1 = 0
    · simp only [hz, ↓reduceIte]
      rw [(h1.z_zero_iff hC).mp hz, infinity_add']
      exact J2
    · simp only [hz, ↓reduceIte]
      have he1 : 1 ≤ e := by
        rcases Nat.eq_zero_or_pos e with rfl | h
        · exact absurd ((h1.z_zero_iff hC).mpr (by rw [Nat.mul_zero, Window5.mul_zero_pt])) hz
        · exact h
      rw [← he, ← hk'] at he1
      obtain ⟨ne1, ne2⟩ := Window5.loop_noexc hC hO hP hP0 hn17 hn64 hk hi he1
      rw [hk', he] at ne1 ne2
      have hh : X2 * (Z1 * Z1) - X1 * (Z2 * Z2) ≠ 0 := by
        intro hx
        by_cases hy : Y2 * Z1 * (Z1 * Z1) - Y1 * Z2 * (Z2 * Z2) = 0
        · exact ne1 (h1.same hC J2 hz z2 hx hy)
        · exact ne2 (h1.opposite hC hQ hW J2 hz z2 hx hy)
      exact h1.add_ne hC hM3 hQ hW J2 hz z2 hh

/-- The iteration's result for any `k`: a triple of a point of the curve, which
is `[winE k' J i]P` for `k < n` (`jstep_point`). Beyond `n` an addition may be
exceptional: then `Z = 0`, a triple of `O`. -/
theorem jstep_pt (hC : Law C) (hM3 : AM3 C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) (hn17 : C.n % 32 = 17) (hn64 : 64 ≤ C.n) {k J i : Nat}
    (hi : i < J) {X1 Y1 Z1 X2 Y2 Z2 : Fe C} {Q1 : Point C} (hQ1 : onCurve C Q1 = true)
    (hQ1e : k < C.n → Q1 = mul (32 * Window5.winE (k + 16 * Window5.geom J) J (i + 1)) P)
    (h1 : InvJ C X1 Y1 Z1 Q1)
    (h2 : 1 ≤ magH 16 (Window5.nib (k + 16 * Window5.geom J) i) →
      InvJ C X2 Y2 Z2 (Window5.winPt C P (k + 16 * Window5.geom J) i) ∧ Z2 ≠ 0) :
    ∃ Q : Point C, onCurve C Q = true ∧ (k < C.n → Q = mul (Window5.winE (k + 16 * Window5.geom J) J i) P) ∧
      InvJ C
        (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then X1
          else if Z1 = 0 then X2 else (jacAddF X1 Y1 Z1 X2 Y2 Z2).1)
        (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then Y1
          else if Z1 = 0 then Y2 else (jacAddF X1 Y1 Z1 X2 Y2 Z2).2.1)
        (if magH 16 (Window5.nib (k + 16 * Window5.geom J) i) = 0 then Z1
          else if Z1 = 0 then Z2 else (jacAddF X1 Y1 Z1 X2 Y2 Z2).2.2) Q := by
  by_cases hk : k < C.n
  · refine ⟨_, hC.onCurve_mul hP _, fun _ => rfl, ?_⟩
    rw [hQ1e hk] at h1
    exact jstep_point hC hM3 hO hP hP0 hn17 hn64 hk hi h1 h2
  have nk : ∀ Q : Point C, k < C.n → Q = mul (Window5.winE (k + 16 * Window5.geom J) J i) P :=
    fun _ h' => absurd h' hk
  generalize k + 16 * Window5.geom J = k' at h2 nk ⊢
  by_cases h0 : magH 16 (Window5.nib k' i) = 0
  · simp only [h0, ↓reduceIte]
    exact ⟨Q1, hQ1, nk _, h1⟩
  · simp only [h0, ↓reduceIte]
    obtain ⟨J2, z2⟩ := h2 (by omega)
    have hW : onCurve C (Window5.winPt C P k' i) = true := Window5.onCurve_winPt hC hP k' i
    by_cases hz : Z1 = 0
    · simp only [hz, ↓reduceIte]
      exact ⟨_, hW, nk _, J2⟩
    · simp only [hz, ↓reduceIte]
      by_cases hh : X2 * (Z1 * Z1) - X1 * (Z2 * Z2) = 0
      · refine ⟨.infinity, rfl, nk _, Or.inl ⟨rfl, ?_⟩⟩
        show Z1 * Z2 * (X2 * (Z1 * Z1) - X1 * (Z2 * Z2)) = 0
        rw [hh]; grind
      · exact ⟨_, hC.onCurve_add hQ1 hW, nk _, h1.add_ne hC hM3 hQ1 hW J2 hz z2 hh⟩


end VG.Proof.Weierstrass.Window5
