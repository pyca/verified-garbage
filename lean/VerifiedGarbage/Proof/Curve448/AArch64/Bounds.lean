module

public import VerifiedGarbage.Proof.X448.Wide.Representation
public import VerifiedGarbage.Proof.X448.Wide.Product
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `X448.Wide.SquareProduct`, which only this module used -/

section

/-! Untrusted: symmetric diagonal accumulation for an eight-limb square. -/

@[expose] public section

namespace VG.Proof.X448.Wide

def sqrSum (f : Nat → Nat) (k : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sqrSum f k n + if n ≤ k ∧ k < n + 8 ∧ n ≤ k - n then
      if n = k - n then f n * f (k - n) else 2 * (f n * f (k - n)) else 0

theorem sqrSum_eq (f : Nat → Nat) {k : Nat} (hk : k < 16) :
    sqrSum f k 8 = rows f f 8 k := by
  rw [← colSum_eq]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨
    k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega_using [hk]
  all_goals (simp [sqrSum, colSum] <;> grind)

theorem sqrSum_le {n m : Nat} (hn : n ≤ m) (f : Nat → Nat) (k : Nat) :
    sqrSum f k n ≤ sqrSum f k m := by
  induction m generalizing n with
  | zero =>
    obtain rfl : n = 0 := by omega_using [hn]
    exact Nat.le_refl _
  | succ m ih =>
    by_cases h : n = m + 1
    · subst n; exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega_using [hn, h])) (by rw [sqrSum]; omega_using [])

end VG.Proof.X448.Wide

end

end


@[expose] public section

namespace VG.Proof.Curve448.AArch64
open VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation

theorem rows_bound {f g : Nat → Nat} (hf : Within weakBound f)
    (hg : Within weakBound g) {n : Nat} (hn : n ≤ 8) (k : Nat) :
    rows f g n k ≤ n * (weakBound - 1) ^ 2 := by
  induction n with
  | zero => simp only [rows, Nat.zero_mul, Nat.le_refl]
  | succ n ih =>
    rw [rows, addRow_at]
    have hp := ih (by omega_using [hn])
    split
    · rename_i hk
      have h1 := hf n (by omega_using [hn])
      have h2 := hg (k - n) (by omega_using [hk])
      have hprod : f n * g (k - n) ≤ (weakBound - 1) ^ 2 := by
        rw [Nat.pow_two]
        exact Nat.mul_le_mul (by omega_using [h1]) (by omega_using [h2])
      rw [Nat.succ_mul]; omega_using [ih, hn, hprod]
    · rw [Nat.succ_mul]; omega_using [ih, hn]

theorem sqrSum_bound {f : Nat → Nat} (hf : Within weakBound f)
    {n k : Nat} (hn : n ≤ 8) (hk : k < 16) : sqrSum f k n < 2 ^ 116 := by
  have h := sqrSum_le hn f k
  rw [sqrSum_eq f hk] at h
  exact Nat.lt_of_le_of_lt (Nat.le_trans h (rows_bound hf hf (by decide) k)) (by decide)
end VG.Proof.Curve448.AArch64
