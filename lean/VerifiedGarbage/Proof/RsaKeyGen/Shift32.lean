module

public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

/-! # One native word supplies its bits from most to least significant -/

@[expose] public section
namespace VG.Proof.RsaKeyGen

theorem shift_step32 (x k i : Nat) (hki : k + i = 31) :
    (x % 2 ^ (k + 1)) * 2 ^ i < 2 ^ 32 ∧
    (decide (2 ^ 32 ≤ (x % 2 ^ (k + 1)) * 2 ^ i + (x % 2 ^ (k + 1)) * 2 ^ i)).toNat = x / 2 ^ k % 2 ∧
    ((x % 2 ^ (k + 1)) * 2 ^ i + (x % 2 ^ (k + 1)) * 2 ^ i) % 2 ^ 32 = (x % 2 ^ k) * 2 ^ (i + 1) ∧
    x / 2 ^ (k + 1) * 2 + x / 2 ^ k % 2 = x / 2 ^ k := by
  rw [Nat.mod_pow_succ]
  have hPQ : 2 ^ k * 2 ^ i = 2 ^ 31 := by rw [← Nat.pow_add, hki]
  have hb : x / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by decide)
  have hlow : x % 2 ^ k * 2 ^ i < 2 ^ 31 := by
    rw [← hPQ]; exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.two_pow_pos _)
  have hexp : (x % 2 ^ k + 2 ^ k * (x / 2 ^ k % 2)) * 2 ^ i = x % 2 ^ k * 2 ^ i + 2 ^ 31 * (x / 2 ^ k % 2) := by
    rw [Nat.add_mul, ← hPQ, Nat.mul_right_comm (2 ^ k) _ (2 ^ i)]
  have h2i : x % 2 ^ k * 2 ^ (i + 1) = 2 * (x % 2 ^ k * 2 ^ i) := by
    rw [Nat.pow_succ]; rw [Nat.mul_comm 2, Nat.mul_assoc]
  have hdiv : x / 2 ^ (k + 1) = x / 2 ^ k / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  rw [hexp, h2i, hdiv]
  have hd := Nat.div_add_mod (x / 2 ^ k) 2
  generalize x % 2 ^ k * 2 ^ i = M at hlow ⊢
  generalize x / 2 ^ k % 2 = b at hb hd ⊢
  refine ⟨by omega, ?_, by omega, by omega⟩
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
  · rw [decide_eq_false (by omega)]; rfl
  · rw [decide_eq_true (by omega)]; rfl

end VG.Proof.RsaKeyGen
