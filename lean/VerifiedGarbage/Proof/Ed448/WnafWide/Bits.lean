module

import VerifiedGarbage.Proof.Ed448.WnafWide.Recoding
public import Init.Data.Nat.Bitwise.Lemmas

/-! The bounded lookahead reconstructed from expanded scalar bits. -/

@[expose] public section

namespace VG.Proof.Ed448.WnafWide

def bit (k i : Nat) : Nat := k / 2^i % 2

def look (k i n : Nat) : Nat := k / 2^i % 2^n

theorem bit_lt (k i : Nat) : bit k i < 2 := Nat.mod_lt _ (by decide)

theorem look_zero (k i : Nat) : look k i 0 = 0 := by
  simp only [look, Nat.pow_zero, Nat.mod_one]

theorem look_succ (k i n : Nat) :
    look k i (n+1) = look k i n + 2^n * bit k (i+n) := by
  simp only [look, bit]
  rw [Nat.mod_pow_succ, Nat.pow_add, ← Nat.div_div_eq_div_mul]

theorem look_step (k i n a : Nat) :
    (a*2+bit k (i+n))*2^n + look k i n = a*2^(n+1) + look k i (n+1) := by
  rw [look_succ, Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 2 (2^n), ← Nat.mul_assoc]
  have hc := Nat.mul_comm (2^n) (bit k (i+n))
  omega

theorem bit_shift (k i : Nat) : (k >>> i) &&& 1 = bit k i := by
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rfl

end VG.Proof.Ed448.WnafWide
