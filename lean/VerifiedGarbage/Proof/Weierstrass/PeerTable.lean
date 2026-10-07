import VerifiedGarbage.Proof.Weierstrass.PeerOrder
import VerifiedGarbage.Proof.Weierstrass.JacSecret

/-! Small-multiple bounds used by the secret peer table's incomplete mixed additions. -/
namespace VG.Proof.Weierstrass
open Spec.Weierstrass
variable {C : Curve}

theorem PeerOrder.mul_ne_infinity (hO : PeerOrder C) {P : Point C}
    (hP : onCurve C P=true) (hne : P≠.infinity) {i : Nat} (hi : 0<i) (hin : i<C.n) :
    mul i P≠.infinity := by
  intro he
  have hz : zmul (i : Int) P=zmul (0 : Nat) P := by
    rw [zmul_natCast,zmul_natCast,he]
    rw [Spec.Weierstrass.mul]
    rfl
  have hd := hO.zmul_dvd hP hne hz
  simp only [Int.natCast_zero,Int.sub_zero,Int.natCast_dvd_natCast] at hd
  exact (Nat.not_le_of_lt hin) (Nat.le_of_dvd hi hd)

theorem PeerOrder.mul_ne_peer (hO : PeerOrder C) {P : Point C}
    (hP : onCurve C P=true) (hne : P≠.infinity) {i : Nat} (hi : 1<i) (hin : i<C.n) :
    mul i P≠P := by
  intro he
  have hz : zmul (i : Int) P=zmul (1 : Nat) P := by
    rw [zmul_natCast,zmul_natCast,mul_one_pt,he]
  have hd := hO.zmul_dvd hP hne hz
  have hc : (i : Int)-(1 : Nat)=((i-1 : Nat) : Int) := by omega
  rw [hc,Int.natCast_dvd_natCast] at hd
  have hl := Nat.le_of_dvd (by omega : 0<i-1) hd
  omega

/-- Distinct points with a nonzero sum have distinct Jacobian X ratios. -/
theorem InvJ.x_cross_ne (hC : Law C) {X1 Y1 Z1 X2 Y2 Z2 : Fe C} {P Q : Point C}
    (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (h1 : InvJ C X1 Y1 Z1 P) (h2 : InvJ C X2 Y2 Z2 Q)
    (hz1 : Z1≠0) (hz2 : Z2≠0) (hne : P≠Q)
    (hadd : Spec.Weierstrass.add P Q≠.infinity) : X2*(Z1*Z1)-X1*(Z2*Z2)≠0 := by
  intro hx
  by_cases hy : Y2*Z1*(Z1*Z1)-Y1*Z2*(Z2*Z2)=0
  · exact hne (h1.same hC h2 hz1 hz2 hx hy)
  · exact hadd (h1.opposite hC hP hQ h2 hz1 hz2 hx hy)

/-- Every odd table entry after the first uses [i]P + P with 1 < i and i+1 < n. -/
theorem PeerOrder.table_mixed_inputs (hO : PeerOrder C) (hC : Law C) {P : Point C}
    (hP : onCurve C P=true) (hne : P≠.infinity) {i : Nat} (hi : 1<i) (hin : i+1<C.n)
    {X1 Y1 Z1 X2 Y2 Z2 : Fe C}
    (h1 : InvJ C X1 Y1 Z1 (mul i P)) (h2 : InvJ C X2 Y2 Z2 P) (hAff : Z2=1) :
    Z1≠0 ∧ X2*(Z1*Z1)-X1≠0 := by
  have hn1 := hO.mul_ne_infinity hP hne (by omega : 0<i) (by omega : i<C.n)
  have hz1 : Z1≠0 := fun hz => hn1 ((h1.z_zero_iff hC).mp hz)
  have hz2 : Z2≠0 := by rw [hAff]; exact hC.one_ne_zero
  have hadd : Spec.Weierstrass.add (mul i P) P≠.infinity := by
    have he := hC.add_mul_mul hP i 1
    rw [mul_one_pt] at he
    rw [he]
    exact hO.mul_ne_infinity hP hne (by omega) hin
  have hx := h1.x_cross_ne hC (hC.onCurve_mul hP i) hP h2 hz1 hz2
    (hO.mul_ne_peer hP hne hi (by omega)) hadd
  exact ⟨hz1,by simpa only [hAff,Lean.Grind.Semiring.mul_one] using hx⟩

end VG.Proof.Weierstrass
