module

public import VerifiedGarbage.Proof.X448.Wide.Representation
public import VerifiedGarbage.Proof.X448.Wide.SquareProduct
import VerifiedGarbage.Proof.Framework.Omega

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
