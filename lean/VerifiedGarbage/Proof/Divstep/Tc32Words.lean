module

public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Divstep.Tc32Shr
import Mathlib.Data.Int.ModEq
import Mathlib.Data.BitVec
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! # Signed 32-bit words, shifts, and matrix combinations -/

@[expose] public section

namespace VG.Proof.Divstep.W32

/-- The masked linear combination: unsigned products less `2^32` times the
other factor where a word is negative is the signed combination, modulo `M`,
given `2^32 X' ≡ 2^32 X` (the factor's words but the top). -/
theorem lin_words {M V X X' Y Y' W W' : Int} {c c' : Prop} [Decidable c] [Decidable c']
    (hX : (2 ^ 32 * X') % M = (2 ^ 32 * X) % M) (hY : (2 ^ 32 * Y') % M = (2 ^ 32 * Y) % M)
    (h : (V + 2 ^ 32 * ((if c then X' else 0) + (if c' then Y' else 0))) % M = (W * X + W' * Y) % M) :
    V % M = ((W - if c then 2 ^ 32 else 0) * X + (W' - if c' then 2 ^ 32 else 0) * Y) % M := by
  have h1 : V ≡ W * X + W' * Y - 2 ^ 32 * ((if c then X' else 0) + (if c' then Y' else 0)) [ZMOD M] := by
    have := Int.ModEq.sub_right (2 ^ 32 * ((if c then X' else 0) + (if c' then Y' else 0))) h
    simpa using this
  have h2 : 2 ^ 32 * ((if c then X' else 0) + (if c' then Y' else 0)) ≡
      2 ^ 32 * ((if c then X else 0) + (if c' then Y else 0)) [ZMOD M] := by
    have hX' : 2 ^ 32 * X' ≡ 2 ^ 32 * X [ZMOD M] := hX
    have hY' : 2 ^ 32 * Y' ≡ 2 ^ 32 * Y [ZMOD M] := hY
    split_ifs <;> simp only [mul_add, mul_zero, add_zero, zero_add]
    · exact hX'.add hY'
    · exact hX'
    · exact hY'
    · rfl
  have h3 := h1.trans (Int.ModEq.sub_left _ h2)
  rw [h3]
  congr 1
  split_ifs <;> ring

/-- A word as a signed number. -/
theorem toInt_sgn (w : BitVec 32) : (w.toNat : Int) - (if 2 ^ 31 ≤ w.toNat then 2 ^ 32 else 0) = w.toInt := by
  rw [BitVec.toInt_eq_toNat_cond]
  have := w.isLt
  split_ifs <;> push_cast <;> omega

/-- A small integer's word, as a signed number. -/
theorem toInt_small {u : Int} (h : |u| ≤ 2 ^ 30) : (BitVec.ofInt 32 u).toInt = u := by
  rw [abs_le] at h
  exact BitVec.toInt_ofInt_eq_self (by decide) (by norm_num; omega) (by norm_num; omega)

/-- The combination of congruent numbers. -/
theorem cong_comb {Q u v X Y f g : Int} (hX : X % Q = f % Q) (hY : Y % Q = g % Q) :
    (u * X + v * Y) % Q = (u * f + v * g) % Q :=
  Int.ModEq.add (Int.ModEq.mul_left u hX) (Int.ModEq.mul_left v hY)

/-- A batch's combination of numbers at most `p`. -/
theorem comb_le {u v f g p : Int} (huv : |u| + |v| ≤ 2 ^ 30) (hf : |f| ≤ p) (hg : |g| ≤ p) :
    |u * f + v * g| ≤ 2 ^ 30 * p := by
  have hp : 0 ≤ p := le_trans (abs_nonneg _) hf
  calc |u * f + v * g| ≤ |u| * |f| + |v| * |g| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |u| * p + |v| * p := add_le_add (mul_le_mul_of_nonneg_left hf (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hg (abs_nonneg _))
    _ = (|u| + |v|) * p := by ring
    _ ≤ 2 ^ 30 * p := mul_le_mul_of_nonneg_right huv hp

/-- Within the half range of `L` words, for `p < 2^(32 (L - 1))`. -/
theorem comb_range {u v f g : Int} {p A : Nat} (huv : |u| + |v| ≤ 2 ^ 30) (hf : |f| ≤ p) (hg : |g| ≤ p)
    (hpA : p < A) : -((A * 2 ^ 31 : Nat) : Int) ≤ u * f + v * g ∧ u * f + v * g < ((A * 2 ^ 31 : Nat) : Int) := by
  have h := comb_le huv hf hg
  rw [abs_le] at h
  have hpA' : (p : Int) < A := by exact_mod_cast hpA
  have hp0 : (0 : Int) ≤ p := Int.natCast_nonneg _
  push_cast
  constructor <;> linarith

/-! ## Bounds over a run -/

end VG.Proof.Divstep.W32
