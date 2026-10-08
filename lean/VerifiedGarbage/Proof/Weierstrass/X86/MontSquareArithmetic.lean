import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Impl.Mont.X86.Sparse

/-! # Bounds and accumulated multiples for full-product P-256 REDC -/
namespace VG.Proof.Weierstrass.X86.Mont
open VG VG.Proof.Mont VG.Impl.Mont.X86

/-- The extra high word accommodates the unreduced square and every reduction multiple. -/
theorem square_round_room {i t : Nat} (hi : i < 8)
    (ht : t < 2 ^ (32 * (16 - i)) + p256Prime) :
    t + (2 ^ 32 - 1) * p256Prime < 2 ^ (32 * (17 - i)) := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceSub, Nat.reduceMul, p256Prime] at ht ⊢ <;> omega

/-- Dividing the cancelled low word tightens the same bound for the next round. -/
theorem square_round_bound {i t t' q : Nat} (hi : i < 8) (hq : q < 2 ^ 32)
    (ht : t < 2 ^ (32 * (16 - i)) + p256Prime) (he : 2 ^ 32 * t' = t + q * p256Prime) :
    t' < 2 ^ (32 * (16 - (i + 1))) + p256Prime := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, p256Prime] at ht he ⊢ <;> omega

/-- Append a reduction digit to the accumulated multiple. -/
theorem square_round_multiple {i t t' q U T : Nat} (hq : q < 2 ^ 32)
    (hU : U < 2 ^ (32 * i)) (hT : 2 ^ (32 * i) * t = T + U * p256Prime)
    (he : 2 ^ 32 * t' = t + q * p256Prime) :
    ∃ U', U' < 2 ^ (32 * (i + 1)) ∧ 2 ^ (32 * (i + 1)) * t' = T + U' * p256Prime := by
  refine ⟨U + 2 ^ (32 * i) * q, ?_, ?_⟩
  · have hq' := Nat.mul_le_mul_left (2 ^ (32 * i)) (show q ≤ 2 ^ 32 - 1 by omega)
    rw [pow32_succ]
    have hp : 2 ^ (32 * i) * (2 ^ 32 - 1) + 2 ^ (32 * i) = 2 ^ 32 * 2 ^ (32 * i) := by
      rw [Nat.mul_sub_one, Nat.mul_comm]
      have := Nat.le_mul_of_pos_left (2 ^ (32 * i)) (by decide : 0 < (2 ^ 32 : Nat))
      omega
    omega
  · rw [pow32_succ, Nat.mul_assoc, Nat.mul_left_comm (2 ^ 32), he, Nat.mul_add, hT]
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

/-- A reduced square needs at most one final subtraction. -/
theorem square_final_bound {a t U : Nat} (ha : a < p256Prime) (hU : U < 2 ^ 256)
    (he : 2 ^ 256 * t = a * a + U * p256Prime) : t < 2 * p256Prime := by
  have hp : p256Prime < 2 ^ 256 := by decide
  have haa := Nat.mul_lt_mul_of_lt_of_lt ha (Nat.lt_trans ha hp)
  simp only [p256Prime] at ha hU he hp haa ⊢
  omega

end VG.Proof.Weierstrass.X86.Mont
