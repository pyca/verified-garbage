import VerifiedGarbage.Proof.Weierstrass.Comb

/-!
# The fixed-base comb with `w`-bit digits, on any target

As `Proof/Weierstrass/Comb.lean`, for windows of `w ≥ 1` bits: with `B = 2^w`,
`H = 2^(w-1)` and the digits `d_j = k_j - H` of the windows `k_j` of `k`, the
accumulator after the digits `J - 1` down to `j` is `[combEW w k J j]G`, with
`combEW w k J j = H Σ_{i<j} B^i + Σ_{j≤i<J} k_i B^i` (`combEW_step`): it
starts at `[H Σ_{i<J} B^i]G` and ends at `[k]G` (`combEW_zero`, for
`k < B^J`). Adding `[d_j B^j]G`, an entry of table `j` or its reflection,
takes `[combEW w k J (j+1)]G` to `[combEW w k J j]G` (`combW_add`).

`CombOkW` is what the code needs of its tables: entry `m` of table `j` is
`[(m + 1) B^j]G` for `m < H`, and the start is `[H Σ_{i<J} B^i]G`, affine.
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

variable {C : Curve}

/-- `Σ_{i<j} 2^(w i)`. -/
def geomW (w : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => geomW w j + 2 ^ (w * j)

/-- Window `j` of `k`: its bits `w j`, …, `w j + w - 1`. -/
def combWin (w k j : Nat) : Nat := k / 2 ^ (w * j) % 2 ^ w

/-- The comb's multiple after the digits `J - 1` down to `j`. -/
def combEW (w k J j : Nat) : Nat :=
  2 ^ (w - 1) * geomW w j + k % 2 ^ (w * J) / 2 ^ (w * j) * 2 ^ (w * j)

theorem combWin_lt (w k j : Nat) : combWin w k j < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos _)

theorem combEW_top (w k J : Nat) : combEW w k J J = 2 ^ (w - 1) * geomW w J := by
  rw [combEW, Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)), Nat.zero_mul, Nat.add_zero]

theorem combEW_zero {w k J : Nat} (hk : k < 2 ^ (w * J)) : combEW w k J 0 = k := by
  simp [combEW, geomW, Nat.mod_eq_of_lt hk]

theorem pow_w_succ (w j : Nat) : 2 ^ (w * (j + 1)) = 2 ^ (w * j) * 2 ^ w := by
  rw [Nat.mul_succ, Nat.pow_add]

/-- An iteration: `combEW w k J j + H 2^(wj) = combEW w k J (j+1) + k_j 2^(wj)`. -/
theorem combEW_step {w k J j : Nat} (hj : j < J) :
    combEW w k J j + 2 ^ (w - 1) * 2 ^ (w * j) =
      combEW w k J (j + 1) + combWin w k j * 2 ^ (w * j) := by
  have hq : k % 2 ^ (w * J) / 2 ^ (w * j) % 2 ^ w = combWin w k j := by
    have hdvd : 2 ^ (w * j) * 2 ^ w ∣ 2 ^ (w * J) := by
      rw [← pow_w_succ]; exact Nat.pow_dvd_pow 2 (Nat.mul_le_mul_left _ hj)
    rw [← Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd k hdvd, Nat.mod_mul_right_div_self]
    rfl
  have hd : k % 2 ^ (w * J) / 2 ^ (w * j) =
      k % 2 ^ (w * J) / 2 ^ (w * (j + 1)) * 2 ^ w + combWin w k j := by
    rw [pow_w_succ, ← Nat.div_div_eq_div_mul, ← hq, Nat.div_add_mod']
  simp only [combEW, geomW]
  rw [hd, Nat.add_mul, pow_w_succ]
  have : k % 2 ^ (w * J) / (2 ^ (w * j) * 2 ^ w) * 2 ^ w * 2 ^ (w * j) =
      k % 2 ^ (w * J) / (2 ^ (w * j) * 2 ^ w) * (2 ^ (w * j) * 2 ^ w) := by
    rw [Nat.mul_assoc, Nat.mul_comm (2 ^ w) (2 ^ (w * j))]
  rw [Nat.mul_add] at *
  omega

theorem half_le_combEW {w k J j : Nat} : 2 ^ (w - 1) * 2 ^ (w * j) ≤ combEW w k J (j + 1) := by
  simp only [combEW, geomW, Nat.mul_add]; omega

/-- Entry `m` of table `j` and the start: what the comb needs of its tables
for `G`: `J` tables of `H = 2^(w-1)` entries, entry `m` of table `j` the
affine `[(m + 1) 2^(wj)]G`, and the start the affine `[H Σ_{i<J} 2^(wi)]G`,
with coordinates below `p`. -/
structure CombOkW (C : Curve) (w J : Nat) (tbl : List (List (Nat × Nat))) (start : Nat × Nat) :
    Prop where
  len : tbl.length = J
  lenH : ∀ j < J, (tbl.getD j []).length = 2 ^ (w - 1)
  lt : ∀ j < J, ∀ m < 2 ^ (w - 1), (combAt tbl j m).1 < C.p ∧ (combAt tbl j m).2 < C.p
  entry : ∀ j < J, ∀ m < 2 ^ (w - 1), mul ((m + 1) * 2 ^ (w * j)) (G C) =
    .affine (Fin.ofNat C.p (combAt tbl j m).1) (Fin.ofNat C.p (combAt tbl j m).2)
  start_lt : start.1 < C.p ∧ start.2 < C.p
  start : mul (2 ^ (w - 1) * geomW w J) (G C) =
    .affine (Fin.ofNat C.p start.1) (Fin.ofNat C.p start.2)

/-- The point of magnitude `a ≤ H` in table `j`: `O` for `0`. -/
def combPtW (C : Curve) (w j a : Nat) : Point C := mul (a * 2 ^ (w * j)) (G C)

/-- An iteration's addition: `[combEW (j+1)]G + [d_j 2^(wj)]G = [combEW j]G`,
with `[d_j 2^(wj)]G` the point of magnitude `|d_j|`, reflected for `d_j < 0`. -/
theorem combW_add (hC : Law C) (hG : onCurve C (G C) = true) {w k J j : Nat} (hj : j < J) :
    Spec.Weierstrass.add (mul (combEW w k J (j + 1)) (G C))
      (if 2 ^ (w - 1) ≤ combWin w k j then combPtW C w j (combWin w k j - 2 ^ (w - 1))
        else negPt (combPtW C w j (2 ^ (w - 1) - combWin w k j))) =
      mul (combEW w k J j) (G C) := by
  have hs := combEW_step (w := w) (k := k) hj
  have h8 := half_le_combEW (w := w) (k := k) (J := J) (j := j)
  split
  · rw [combPtW, hC.add_mul_mul hG]
    congr 1
    rw [Nat.sub_mul]
    have : 2 ^ (w - 1) * 2 ^ (w * j) ≤ combWin w k j * 2 ^ (w * j) := Nat.mul_le_mul_right _ ‹_›
    omega
  · rw [combPtW, hC.add_mul_neg hG (by
      rw [Nat.sub_mul]; omega)]
    congr 1
    rw [Nat.sub_mul]
    have : combWin w k j * 2 ^ (w * j) ≤ 2 ^ (w - 1) * 2 ^ (w * j) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

/-- The signed entry of digit `j`: `[d_j 2^(wj)]G` as `combW_add` has it. -/
def signedPtW (C : Curve) (w k j : Nat) : Point C :=
  if 2 ^ (w - 1) ≤ combWin w k j then combPtW C w j (combWin w k j - 2 ^ (w - 1))
  else negPt (combPtW C w j (2 ^ (w - 1) - combWin w k j))

end VG.Proof.Weierstrass
