module

public import VerifiedGarbage.Proof.Rsa.RecoverMath
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Recovering the prime factors: exponentiation in Montgomery form, and masks

`exp_step`: a step of binary exponentiation from the least significant bit,
in Montgomery form; `lt_bit` and `eq_bit`: the 32-bit masks of `a < b` and
`a = b` the code computes.
-/

@[expose] public section

namespace VG.Proof.Rsa

open VG.Proof.Bignum (mont_cancel)

/-- A step of the exponentiation: `y = g^(r mod 2^i)` and `G = g^(2^i)` (in
Montgomery form) times the bit `i` of `r`'s multiplicand, and `G` squared. -/
theorem exp_step {g r i n R Y G X Y' G' : Nat} (hR : Nat.Coprime R n)
    (hY : Y = g ^ (r % 2 ^ i) * R % n) (hG : G = g ^ (2 ^ i) * R % n)
    (hX : X = if r / 2 ^ i % 2 = 0 then R % n else G)
    (hY' : Y' < n) (hY'v : Y' * R % n = Y * X % n) (hG' : G' < n) (hG'v : G' * R % n = G * G % n) :
    Y' = g ^ (r % 2 ^ (i + 1)) * R % n ∧ G' = g ^ (2 ^ (i + 1)) * R % n := by
  have hYm : Y % n = g ^ (r % 2 ^ i) * R % n := by rw [hY, Nat.mod_mod]
  have hGm : G % n = g ^ (2 ^ i) * R % n := by rw [hG, Nat.mod_mod]
  have hXm : X % n = g ^ (r / 2 ^ i % 2 * 2 ^ i) * R % n := by
    rw [hX]
    split
    · rename_i h; rw [h, Nat.zero_mul, Nat.pow_zero, Nat.one_mul, Nat.mod_mod]
    · rename_i h; rw [show r / 2 ^ i % 2 = 1 by omega, Nat.one_mul, hGm]
  refine ⟨?_, ?_⟩
  · have := mont_mulp hR hYm hXm hY'v
    rw [Nat.mod_eq_of_lt hY'] at this
    rw [this, Nat.mod_pow_succ, Nat.mul_comm (2 ^ i)]
  · have := mont_mulp hR hGm hGm hG'v
    rw [Nat.mod_eq_of_lt hG'] at this
    rw [this, ← Nat.two_mul, Nat.pow_succ, Nat.mul_comm (2 ^ i)]

/-- A Montgomery product of two powers. -/
theorem mont_prod_eq (x a b R n : Nat) :
    x ^ (a + b) * R % n * R % n = (x ^ a * R % n) * (x ^ b * R % n) % n := by
  rw [Nat.mod_mul_mod, ← Nat.mul_mod, Nat.pow_add, Nat.mul_mul_mul_comm, Nat.mul_assoc (x ^ a * x ^ b)]

/-- The multiplicand of a bit: `x^0` or `x^(2^i)` in Montgomery form. -/
theorem bit_mont (x r i R n : Nat) :
    (if r / 2 ^ i % 2 = 0 then R % n else x ^ (2 ^ i) * R % n) = x ^ (r / 2 ^ i % 2 * 2 ^ i) * R % n := by
  split
  · rename_i h; rw [h, Nat.zero_mul, Nat.pow_zero, Nat.one_mul]
  · rename_i h; rw [show r / 2 ^ i % 2 = 1 by omega, Nat.one_mul]

/-- The bits of `r` up to `i + 1`. -/
theorem mod_pow_succ' (r i : Nat) : r % 2 ^ (i + 1) = r % 2 ^ i + r / 2 ^ i % 2 * 2 ^ i := by
  rw [Nat.mod_pow_succ, Nat.mul_comm]

/-- The top bit of `a - b`: `a < b`, for `a, b < 2^31`. -/
theorem lt_bit {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    ((BitVec.ofNat 32 a - BitVec.ofNat 32 b) >>> 31).toNat = if a < b then 1 else 0 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (a := b) (by omega)]
  split <;> omega

/-- The top bit of `(a xor b) - 1`: `a = b`, for `a, b < 2^31`. -/
theorem eq_bit {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    (((BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b) - 1) >>> 31).toNat = if a = b then 1 else 0 := by
  have hx : (BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b).toNat = a ^^^ b := by
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a) (by omega),
      Nat.mod_eq_of_lt (a := b) (by omega)]
  have hlt : a ^^^ b < 2 ^ 31 := Nat.xor_lt_two_pow ha hb
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, hx,
    show (1 : BitVec 32).toNat = 1 from rfl]
  by_cases e : a = b
  · subst e; rw [Nat.xor_self]; simp
  · have hne : BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b ≠ 0#32 := fun h => e (by
      have := congrArg BitVec.toNat (BitVec.xor_eq_zero_iff.mp h)
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a) (by omega),
        Nat.mod_eq_of_lt (a := b) (by omega)] at this
      exact this)
    have : a ^^^ b ≠ 0 := fun h => hne (BitVec.eq_of_toNat_eq (by rw [hx, h]; rfl))
    simp only [e, ite_false]
    omega

end VG.Proof.Rsa
