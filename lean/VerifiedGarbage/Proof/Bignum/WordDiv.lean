module
-- separate module: target-independent, for every target's division by words (AArch64's, PPC64LE's, x86's)
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Multiword arithmetic: long division, a word at a time

`X mod m` by the steps `r := (r 2^W + u) mod m` over the words `u` of `X`
(of `W` bits), most significant first (Knuth, TAOCP vol. 2, §4.3.1,
Algorithm D), independent of the target and of the word width: after the
step of word `n`, `r = ⌊X / 2^(W n)⌋ mod m` (`wordDiv_step`); it starts at
`⌊X / 2^(W n)⌋` itself while that is below `m` (`wordDiv_top`), and ends at
`X mod m` after word 0 (`wordDiv_zero`). A step's own arithmetic is
`WordStep.wordStepQ1_div` (for `W = 64`).
-/

@[expose] public section

namespace VG.Proof.Bignum.WordStep

/-- `⌊X / 2^(W n)⌋` is `⌊X / 2^(W (n + 1))⌋` shifted up a word, plus word `n`. -/
theorem wordDiv_digits (X W n : Nat) :
    X / 2 ^ (W * n) = X / 2 ^ (W * (n + 1)) * 2 ^ W + X / 2 ^ (W * n) % 2 ^ W := by
  rw [Nat.mul_succ, Nat.pow_add, ← Nat.div_div_eq_div_mul, Nat.mul_comm (X / 2 ^ (W * n) / 2 ^ W),
    Nat.div_add_mod]

/-- A step: `r = ⌊X / 2^(W (n + 1))⌋ mod m` shifted up a word plus word `n`
of `X`, modulo `m`, is `⌊X / 2^(W n)⌋ mod m`. -/
theorem wordDiv_step (X m W n : Nat) :
    (X / 2 ^ (W * (n + 1)) % m * 2 ^ W + X / 2 ^ (W * n) % 2 ^ W) % m = X / 2 ^ (W * n) % m := by
  conv => rhs; rw [wordDiv_digits X W n]
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

/-- `wordDiv_step` for a remainder `r` and a word `u` given by their values. -/
theorem wordDiv_step' {X m W n r u : Nat} (hr : r = X / 2 ^ (W * (n + 1)) % m)
    (hu : u = X / 2 ^ (W * n) % 2 ^ W) : (r * 2 ^ W + u) % m = X / 2 ^ (W * n) % m := by
  rw [hr, hu, wordDiv_step]

/-- The start: the top words `⌊X / 2^(W n)⌋`, below `m`, are their remainder. -/
theorem wordDiv_top {X m W n : Nat} (h : X / 2 ^ (W * n) < m) : X / 2 ^ (W * n) % m = X / 2 ^ (W * n) :=
  Nat.mod_eq_of_lt h

/-- The end: after word 0, `X mod m`. -/
theorem wordDiv_zero (X W : Nat) : X / 2 ^ (W * 0) = X := by
  rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one]

end VG.Proof.Bignum.WordStep
