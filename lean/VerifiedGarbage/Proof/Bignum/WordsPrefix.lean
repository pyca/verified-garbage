module

public import VerifiedGarbage.Proof.Mont.Words32

/-! # The low half of a double-width integer -/

@[expose] public section
namespace VG.Proof.Bignum
open VG VG.Proof.Mont

theorem wordsVal_low_half (m : Mem) (base : Addr) (d n : Nat) :
    wordsVal m base d n = wordsVal m base d (2 * n) % 2 ^ (64 * n) := by
  rw [wordsVal_eq_val32, wordsVal_eq_val32,
    show 2 * (2 * n) = 2 * n + 2 * n by omega, val32_append,
    show 64 * n = 32 * (2 * n) by omega, Nat.add_mod, Nat.mul_mod_right,
    Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt (val32_lt _ _ _ _)]

/-- The low `h` words of an `n`-word integer. -/
theorem wordsVal_prefix (m : Mem) (base : Addr) (d : Nat) {h n : Nat} (hh : h ≤ n) :
    wordsVal m base d h = wordsVal m base d n % 2 ^ (64 * h) := by
  rw [wordsVal_eq_val32, wordsVal_eq_val32, show 2 * n = 2 * h + 2 * (n - h) by omega,
    val32_append, show 64 * h = 32 * (2 * h) by omega, Nat.add_mod, Nat.mul_mod_right,
    Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt (val32_lt _ _ _ _)]

/-- Words that are zero together are zero apart. -/
theorem val32_zero_split {m : Mem} {base : Addr} {d j k : Nat} (h : val32 m base d (j + k) = 0) :
    val32 m base d j = 0 ∧ val32 m base (d + 4 * j) k = 0 := by
  rw [val32_append] at h
  have pos := Nat.two_pow_pos (32 * j)
  constructor
  · omega
  · by_contra H
    have := Nat.mul_le_mul_left (2 ^ (32 * j)) (show 1 ≤ val32 m base (d + 4 * j) k by omega)
    omega

end VG.Proof.Bignum
