module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTakeBit

/-! Bounds and prefix arithmetic for pending window digits. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive

theorem pending_lt16 {b v : Nat} (hb : b < 5) (hv : v < 2 ^ b) : v < 16 := by
  have h := Nat.pow_le_pow_right (n := 2) (by decide) (show b ≤ 4 by omega)
  omega_using [h,hv]

theorem pending_bounds {b v bit : Nat} (hb : b < 5) (hv : v < 2 ^ b) (hbit : bit < 2) :
    nextPending b < 5 ∧ nextDigit b (2 * v + bit) < 2 ^ nextPending b := by
  by_cases h4 : b = 4
  · simp [nextPending,nextDigit,h4]
  · simp only [nextPending,nextDigit,ite_eq_right h4,Nat.pow_succ]
    constructor <;> omega_using [hb,h4,hv,hbit]

theorem pending_prefix (b E v bit : Nat) :
    nextExponent b E (2 * v + bit) * 2 ^ nextPending b + nextDigit b (2 * v + bit) =
      2 * (E * 2 ^ b + v) + bit := by
  by_cases h4 : b = 4
  · subst b
    simp only [nextExponent,nextPending,nextDigit,ite_true]
    omega
  · simp only [nextExponent,nextPending,nextDigit,ite_eq_right h4,Nat.pow_succ]
    rw [← Nat.mul_assoc]
    omega

theorem pending_count {b : Nat} (hb : b < 5) : nextPending b = (b + 1) % 5 := by
  by_cases h : b = 4
  · subst b; rfl
  · simp only [nextPending, ite_eq_right h]
    omega

theorem byte_bit_step (V : Nat) {i : Nat} (hi : i < 8) :
    2 * (V / 2 ^ (8 - i)) + V / 2 ^ (7 - i) % 2 = V / 2 ^ (7 - i) := by
  rw [show 8 - i = (7 - i) + 1 by omega, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  omega

theorem tail_prefix_step (K V : Nat) {i : Nat} (hi : i < 8) :
    2 * (K * 2 ^ i + V / 2 ^ (8 - i)) + V / 2 ^ (7 - i) % 2 =
      K * 2 ^ (i + 1) + V / 2 ^ (8 - (i + 1)) := by
  have h := byte_bit_step V hi
  rw [Nat.pow_succ, ← Nat.mul_assoc, show 8 - (i + 1) = 7 - i by omega]
  omega_using [h]

end VG.Proof.Bignum.AArch64.WindowFive
