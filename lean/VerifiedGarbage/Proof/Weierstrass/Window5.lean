import VerifiedGarbage.Proof.Weierstrass.Window
import VerifiedGarbage.Proof.Weierstrass.CombW
import VerifiedGarbage.Proof.Weierstrass.CombDigitW
import VerifiedGarbage.Proof.Framework.PowLit

/-! Signed five-bit windows for public P-256 verification scalars. -/

namespace VG.Proof.Weierstrass.Window5

open Spec.Weierstrass

variable {C : Curve}

def geom : Nat → Nat
  | 0 => 0
  | j + 1 => geom j + 32 ^ j

def nib (k j : Nat) : Nat := k / 32 ^ j % 32

theorem geom_succ_left (m : Nat) : geom (m + 1) = 1 + 32 * geom m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show geom (m + 1) + 32 ^ (m + 1) = 1 + 32 * (geom m + 32 ^ m)
    rw [ih, Nat.pow_succ]
    omega

theorem geom_add (j m : Nat) : geom (j + m) = geom j + 32 ^ j * geom m := by
  induction m with
  | zero => simp [geom]
  | succ m ih =>
    show geom (j + m) + 32 ^ (j + m) = geom j + 32 ^ j * (geom m + 32 ^ m)
    rw [ih, Nat.mul_add, Nat.pow_add]
    omega

theorem geom_mul (j : Nat) : 31 * geom j + 1 = 32 ^ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show 31 * (geom j + 32 ^ j) + 1 = 32 ^ (j + 1)
    rw [Nat.pow_succ]; omega

/-- `16 Σ_{i<j} 32^i < 32^j`. -/
theorem half_geom_lt (j : Nat) : 16 * geom j < 32 ^ j := by
  have := geom_mul j; omega

/-- The window method's multiple after the digits `J - 1` down to `j`. -/
def winE (k J j : Nat) : Nat := k / 32 ^ j - 16 * geom (J - j)

/-- The digits above `j` sum to a natural number. -/
theorem geom_le_div {k J j : Nat} (hk : 16 * geom J ≤ k) (hj : j ≤ J) :
    16 * geom (J - j) ≤ k / 32 ^ j := by
  have hpos : 0 < 32 ^ j := Nat.pow_pos (by decide)
  have e : 16 * geom J = 16 * geom j + 32 ^ j * (16 * geom (J - j)) := by
    have := geom_add j (J - j)
    rw [Nat.add_sub_cancel' hj] at this
    rw [this]; grind
  rw [Nat.le_div_iff_mul_le hpos]
  have := half_geom_lt j
  rw [Nat.mul_comm]
  omega

theorem winE_top {k J : Nat} (hk : k < 32 ^ J) : winE k J J = 0 := by
  simp [winE, Nat.div_eq_of_lt hk]

theorem winE_zero (k J : Nat) : winE k J 0 = k - 16 * geom J := by
  simp [winE]

/-- An iteration: `winE k J j + 16 = 32 winE k J (j+1) + k_j`. -/
theorem winE_step {k J j : Nat} (hk : 16 * geom J ≤ k) (hj : j < J) :
    winE k J j + 16 = 32 * winE k J (j + 1) + nib k j := by
  have h₁ := geom_le_div hk (Nat.le_of_lt hj)
  have h₂ := geom_le_div hk (j := j + 1) hj
  have hd : k / 32 ^ j = 32 * (k / 32 ^ (j + 1)) + nib k j := by
    rw [nib, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    have := Nat.div_add_mod (k / 32 ^ j) 32
    omega
  have hg : geom (J - j) = 1 + 32 * geom (J - (j + 1)) := by
    rw [show J - j = J - (j + 1) + 1 by omega, geom_succ_left]
  simp only [winE]
  rw [hg] at h₁ ⊢
  omega

/-- The point of digit `j`: `[k_j - 16]P`, as `[|d_j|]P` reflected for `d_j < 0`. -/
def winPt (C : Curve) (P : Point C) (k j : Nat) : Point C :=
  if 16 ≤ nib k j then mul (nib k j - 16) P else negPt (mul (16 - nib k j) P)

/-- An iteration's addition: `[32 winE k J (j+1)]P + [d_j]P = [winE k J j]P`. -/
theorem win_add (hC : Law C) {P : Point C} (hP : onCurve C P = true) {k J j : Nat}
    (hk : 16 * geom J ≤ k) (hj : j < J) :
    Spec.Weierstrass.add (mul (32 * winE k J (j + 1)) P) (winPt C P k j) = mul (winE k J j) P := by
  have hs := winE_step hk hj
  unfold winPt
  split
  · rw [hC.add_mul_mul hP]
    congr 1
    omega
  · rw [hC.add_mul_neg hP (by omega)]
    congr 1
    omega

theorem onCurve_winPt (hC : Law C) {P : Point C} (hP : onCurve C P = true) (k j : Nat) :
    onCurve C (winPt C P k j) = true := by
  unfold winPt
  split
  · exact hC.onCurve_mul hP _
  · exact onCurve_negPt (hC.onCurve_mul hP _)

/-- A P-256 scalar plus the signed-digit offset fits in 52 five-bit windows. -/
theorem recode_lt {k : Nat} (hk : k < 2 ^ 256) :
    k + 16 * geom 52 < 32 ^ 52 := by
  have h := geom_mul 52
  omega

/-- The offset used by the machine implementation. -/
theorem offset_eq : 16 * geom 52 = 16 * ((32 ^ 52 - 1) / 31) := by
  have h := geom_mul 52
  omega

/-- The common bit reader reads exactly the five-bit window used here. -/
theorem combWin_five (k j : Nat) : combWin 5 k j = nib k j := by
  simp only [combWin,nib,show 32=2^5 from rfl,← Nat.pow_mul]

/-- A zero signed digit contributes the identity point. -/
theorem winPt_zero {P : Point C} {k j : Nat} (h : magH 16 (nib k j)=0) :
    winPt C P k j = .infinity := by
  have he : nib k j=16 := by unfold magH at h; split at h <;> omega
  simp only [winPt,he,Nat.le_refl,ite_true,Nat.sub_self]
  rw [Spec.Weierstrass.mul]; simp

/-- The loaded magnitude is reflected precisely for a negative digit. -/
theorem winPt_mag (P : Point C) (k j : Nat) :
    winPt C P k j = if decide (nib k j<16) then
      negPt (mul (magH 16 (nib k j)) P) else mul (magH 16 (nib k j)) P := by
  unfold winPt magH
  by_cases h : 16 ≤ nib k j
  · simp [h,show ¬nib k j<16 by omega]
  · simp [h,show nib k j<16 by omega]

end VG.Proof.Weierstrass.Window5
