import VerifiedGarbage.Proof.Weierstrass.Window5
import VerifiedGarbage.Proof.Weierstrass.PeerOrder
import Mathlib.Data.Nat.ModEq

/-! Noncollision bounds for secret centered radix-32 multiplication. -/
namespace VG.Proof.Weierstrass.Window5
open Spec.Weierstrass
variable {C : Curve}

/-- The remaining prefix depends only on the original scalar and j. -/
theorem winE_recode (k : Nat) {J j : Nat} (hj : j ≤ J) :
    winE (k + 16 * geom J) J j = (k + 16 * geom j) / 32 ^ j := by
  have hg := geom_add j (J - j)
  rw [Nat.add_sub_cancel' hj] at hg
  have he : k + 16 * geom J = (k + 16 * geom j) + 32 ^ j * (16 * geom (J-j)) := by
    rw [hg]
    grind
  rw [winE, he, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)), Nat.add_sub_cancel]

theorem winE_recode_le (k : Nat) {J j : Nat} (hj : j ≤ J) :
    winE (k + 16 * geom J) J j ≤ k / 32 ^ j + 1 := by
  rw [winE_recode k hj]
  have h := Nat.add_div_le_div_add_div_add_one k (16 * geom j) (32 ^ j)
  simpa only [Nat.div_eq_of_lt (half_geom_lt j), Nat.add_zero] using h

theorem winE_early_le (k : Nat) {J j : Nat} (hj : j ≤ J) (hj2 : 2 ≤ j) :
    winE (k + 16 * geom J) J j ≤ k / 1024 + 1 := by
  have hp : 1024 ≤ 32 ^ j := Nat.pow_le_pow_right (n := 32) (by decide) hj2
  exact (winE_recode_le k hj).trans (Nat.add_le_add_right (Nat.div_le_div_left hp (by decide)) 1)

/-- At the last addition, n mod 32 = 17 excludes the equal-point case. -/
theorem last_not_dvd {n k a r : Nat} (hn : 64 ≤ n) (hnmod : n % 32 = 17)
    (hk : k < n) (ha : 0 < a) (hr : r < 32) (hs : k + 16 = 32 * a + r) :
    ¬ n ∣ 32 * a + 16 - r := by
  intro hd
  have hp : 0 < 32 * a + 16 - r := by omega
  have hl : 32 * a + 16 - r < n * 2 := by omega
  obtain ⟨q, hq⟩ := hd
  rw [hq] at hp hl
  have hq2 : q < 2 := (Nat.mul_lt_mul_left (by omega : 0 < n)).mp hl
  have hq1 : q = 1 := by
    by_contra he
    have hq0 : q = 0 := by omega
    simp only [hq0, Nat.mul_zero, Nat.lt_irrefl] at hp
  rw [hq1, Nat.mul_one] at hq
  omega

/-- Earlier prefixes are too small for a collision modulo n. -/
theorem early_not_dvd {n k a r : Nat} (hn : 64 ≤ n) (hk : k < n)
    (ha : 0 < a) (hr : r < 32) (hb : a ≤ k / 1024 + 1) :
    ¬ n ∣ 32 * a + 16 - r := by
  intro hd
  have hp : 0 < 32 * a + 16 - r := by omega
  have hl := Nat.le_of_dvd hp hd
  omega

theorem cast_sub_digit {a r : Nat} (ha : 0 < a) (hr : r < 32) :
    32 * (a : Int) - ((r : Int) - 16) = ((32 * a + 16 - r : Nat) : Int) := by
  rw [Int.natCast_sub (by omega : r ≤ 32 * a + 16)]
  simp only [Int.natCast_add, Int.natCast_mul]
  omega

/-- Every addition in the centered radix-32 loop avoids equal nonzero multiples. -/
theorem window_not_dvd {n k J j : Nat} (hn : 64 ≤ n) (hnmod : n % 32 = 17)
    (hk : k < n) (hj : j < J) (ha : 0 < winE (k + 16 * geom J) J (j+1)) :
    ¬ (n : Int) ∣ 32 * (winE (k + 16 * geom J) J (j+1) : Int) -
      ((nib (k + 16 * geom J) j : Int) - 16) := by
  have hr : nib (k + 16 * geom J) j < 32 := Nat.mod_lt _ (by decide)
  rw [cast_sub_digit ha hr, Int.natCast_dvd_natCast]
  by_cases hj0 : j = 0
  · subst j
    have hs := winE_step (k := k + 16 * geom J) (by omega) hj
    rw [winE_zero, Nat.add_sub_cancel] at hs
    exact last_not_dvd hn hnmod hk ha hr hs
  · exact early_not_dvd hn hk ha hr (winE_early_le k hj (by omega))

theorem winPt_zmul (P : Point C) (k j : Nat) :
    winPt C P k j = zmul ((nib k j : Int) - 16) P := by
  unfold winPt zmul
  split
  next h =>
    rw [ite_eq_left (by omega : 0 ≤ (nib k j : Int) - 16)]
    exact congrArg (fun m => mul m P) (by omega)
  next h =>
    rw [ite_eq_right (by omega : ¬ 0 ≤ (nib k j : Int) - 16)]
    exact congrArg (fun m => negPt (mul m P)) (by omega)

/-- The point-level hypothesis required by masked Jacobian addition. -/
theorem window_ne (hO : PeerOrder C) {P : Point C} (hP : onCurve C P = true)
    (hne : P ≠ .infinity) (hn : 64 ≤ C.n) (hnmod : C.n % 32 = 17)
    {k J j : Nat} (hk : k < C.n) (hj : j < J)
    (hacc : mul (32 * winE (k + 16 * geom J) J (j+1)) P ≠ .infinity) :
    mul (32 * winE (k + 16 * geom J) J (j+1)) P ≠ winPt C P (k + 16 * geom J) j := by
  intro he
  have ha : 0 < winE (k + 16 * geom J) J (j+1) := by
    by_contra h
    have hz : winE (k + 16 * geom J) J (j+1) = 0 := by omega
    apply hacc
    rw [hz, Nat.mul_zero, Spec.Weierstrass.mul]
    rfl
  rw [winPt_zmul, ← zmul_natCast] at he
  have hd := hO.zmul_dvd hP hne he
  apply window_not_dvd hn hnmod hk hj ha
  simpa only [Int.natCast_mul, Nat.cast_ofNat] using hd

end VG.Proof.Weierstrass.Window5
