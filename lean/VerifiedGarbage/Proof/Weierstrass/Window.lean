import VerifiedGarbage.Proof.Weierstrass.Comb
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Scalar multiplication by signed windows, on any target

For `k' = k + 8 Σ_{i<J} 16^i` with `k' < 16^J` and the digits
`d_i = k'_i - 8` of its nibbles, the window method's accumulator after the
digits `J - 1` down to `j` is `[winE k' J j]P`, with
`winE k' J j = Σ_{i≥j} d_i 16^(i-j) = k' / 16^j - 8 Σ_{i<J-j} 16^i`, which is a
natural number (`geom_le_div`): it starts at `0` (`winE_top`) and ends at `k`
(`winE_zero`). An iteration multiplies it by 16 and adds `d_j`
(`winE_step`), so four doublings and the addition of `[|d_j|]P`, reflected
for `d_j < 0`, take `[winE k' J (j+1)]P` to `[winE k' J j]P` (`win_add`).
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

variable {C : Curve}

theorem geom_succ_left (m : Nat) : geom (m + 1) = 1 + 16 * geom m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show geom (m + 1) + 16 ^ (m + 1) = 1 + 16 * (geom m + 16 ^ m)
    rw [ih, Nat.pow_succ]
    omega

theorem geom_add (j m : Nat) : geom (j + m) = geom j + 16 ^ j * geom m := by
  induction m with
  | zero => simp [geom]
  | succ m ih =>
    show geom (j + m) + 16 ^ (j + m) = geom j + 16 ^ j * (geom m + 16 ^ m)
    rw [ih, Nat.mul_add, Nat.pow_add]
    omega

theorem geom_mul (j : Nat) : 15 * geom j + 1 = 16 ^ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show 15 * (geom j + 16 ^ j) + 1 = 16 ^ (j + 1)
    rw [Nat.pow_succ]; omega

/-- `8 Σ_{i<j} 16^i < 16^j`. -/
theorem eight_geom_lt (j : Nat) : 8 * geom j < 16 ^ j := by
  have := geom_mul j; omega

/-- The window method's multiple after the digits `J - 1` down to `j`. -/
def winE (k J j : Nat) : Nat := k / 16 ^ j - 8 * geom (J - j)

/-- The digits above `j` sum to a natural number. -/
theorem geom_le_div {k J j : Nat} (hk : 8 * geom J ≤ k) (hj : j ≤ J) :
    8 * geom (J - j) ≤ k / 16 ^ j := by
  have hpos : 0 < 16 ^ j := Nat.pow_pos (by decide)
  have e : 8 * geom J = 8 * geom j + 16 ^ j * (8 * geom (J - j)) := by
    have := geom_add j (J - j)
    rw [Nat.add_sub_cancel' hj] at this
    rw [this]; grind
  rw [Nat.le_div_iff_mul_le hpos]
  have := eight_geom_lt j
  rw [Nat.mul_comm]
  omega

theorem winE_top {k J : Nat} (hk : k < 16 ^ J) : winE k J J = 0 := by
  simp [winE, Nat.div_eq_of_lt hk]

theorem winE_zero (k J : Nat) : winE k J 0 = k - 8 * geom J := by
  simp [winE]

/-- An iteration: `winE k J j + 8 = 16 winE k J (j+1) + k_j`. -/
theorem winE_step {k J j : Nat} (hk : 8 * geom J ≤ k) (hj : j < J) :
    winE k J j + 8 = 16 * winE k J (j + 1) + nib k j := by
  have h₁ := geom_le_div hk (Nat.le_of_lt hj)
  have h₂ := geom_le_div hk (j := j + 1) hj
  have hd : k / 16 ^ j = 16 * (k / 16 ^ (j + 1)) + nib k j := by
    rw [nib, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    have := Nat.div_add_mod (k / 16 ^ j) 16
    omega
  have hg : geom (J - j) = 1 + 16 * geom (J - (j + 1)) := by
    rw [show J - j = J - (j + 1) + 1 by omega, geom_succ_left]
  simp only [winE]
  rw [hg] at h₁ ⊢
  omega

/-- `[a]P + [a]P = [2a]P`. -/
theorem Law.double (hC : Law C) {P : Point C} (hP : onCurve C P = true) (a : Nat) :
    Spec.Weierstrass.add (mul a P) (mul a P) = mul (2 * a) P := by
  rw [hC.add_mul_mul hP, Nat.two_mul]

/-- The point of digit `j`: `[k_j - 8]P`, as `[|d_j|]P` reflected for `d_j < 0`. -/
def winPt (C : Curve) (P : Point C) (k j : Nat) : Point C :=
  if 8 ≤ nib k j then mul (nib k j - 8) P else negPt (mul (8 - nib k j) P)

/-- An iteration's addition: `[16 winE k J (j+1)]P + [d_j]P = [winE k J j]P`. -/
theorem win_add (hC : Law C) {P : Point C} (hP : onCurve C P = true) {k J j : Nat}
    (hk : 8 * geom J ≤ k) (hj : j < J) :
    Spec.Weierstrass.add (mul (16 * winE k J (j + 1)) P) (winPt C P k j) = mul (winE k J j) P := by
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

/-- The recoded scalar: `k + 8 Σ_{i<J} 16^i < 16^J` for `k < 2^(64 n)`, with
`J = 16 n + 1`. -/
theorem recode_lt {k n : Nat} (hk : k < 2 ^ (64 * n)) :
    k + 8 * geom (16 * n + 1) < 16 ^ (16 * n + 1) := by
  have h16 : (16 : Nat) ^ (16 * n) = 2 ^ (64 * n) := by
    rw [show (16 : Nat) = 2 ^ 4 by rfl, ← Nat.pow_mul]; congr 1; omega
  have := eight_geom_lt (16 * n)
  rw [h16] at this
  show k + 8 * (geom (16 * n) + 16 ^ (16 * n)) < 16 ^ (16 * n + 1)
  rw [Nat.pow_succ, h16]
  omega

/-- The recoded scalar of `len` bytes: `k + 8 Σ_{j<J} 16^j < 16^J` for
`k < 2^(8 len)`, with `J = 2 len + 1`. -/
theorem recode_lt_len {k len : Nat} (hk : k < 2 ^ (8 * len)) :
    k + 8 * geom (2 * len + 1) < 16 ^ (2 * len + 1) := by
  have h16 : (16 : Nat) ^ (2 * len) = 2 ^ (8 * len) := by
    rw [show (16 : Nat) = 2 ^ 4 by rfl, ← Nat.pow_mul, show 4 * (2 * len) = 8 * len by omega]
  have := eight_geom_lt (2 * len)
  rw [h16] at this
  show k + 8 * (geom (2 * len) + 16 ^ (2 * len)) < 16 ^ (2 * len + 1)
  rw [Nat.pow_succ, h16]
  omega

end VG.Proof.Weierstrass
