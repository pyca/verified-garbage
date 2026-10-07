import VerifiedGarbage.Proof.Mont.Words32

/-! # Arithmetic for the 30-bit divstep shift -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.Proof.Mont

theorem shr_arith32 (j V s t : Nat) (hV : V < 2 ^ (32 * j)) :
    ((V + 2 ^ (32 * j) * s + 2 ^ (32 * j) * 2 ^ 32 * t) / 2 ^ 30) % (2 ^ (32 * j) * 2 ^ 32) =
      ((V + 2 ^ (32 * j) * s) / 2 ^ 30) % 2 ^ (32 * j) + 2 ^ (32 * j) * ((s / 2 ^ 30 + 2 ^ 2 * t) % 2 ^ 32) := by
  generalize 2 ^ (32 * j) = A at *
  have hA0 : 0 < A := by omega
  have e1 : A * 2 ^ 32 * t = 2 ^ 30 * (A * (2 ^ 2 * t)) := by
    rw [show (2 : Nat) ^ 32 = 2 ^ 30 * 2 ^ 2 from rfl, Nat.mul_comm A, Nat.mul_assoc, Nat.mul_assoc,
      Nat.mul_left_comm A]
  have e2 : (V + A * s) / A = s := by
    rw [Nat.add_mul_div_left _ _ hA0, Nat.div_eq_of_lt hV, Nat.zero_add]
  rw [e1, Nat.add_mul_div_left _ _ (by decide), Nat.mod_mul, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ hA0, Nat.div_div_eq_div_mul, Nat.mul_comm (2 ^ 30), ← Nat.div_div_eq_div_mul, e2]

end VG.Proof.Weierstrass.X86.Inv
