module
-- separate module: names no ISA and imports no algebra, so each target's batched inverse over 64-bit words shares its arithmetic

import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

/-! # The arithmetic of the batched inverse's top words

The top word of a value of `ν + 1` words is signed. A shift by 59 and a
Montgomery reduction each read it as a word, and these lemmas give the value
they compute. `Proof/Divstep/TcS.lean` reads it as an integer
(`shr_nat`, `mredRaw_nat`). The lemmas are over `Nat`: each target states
its own instructions' values in that form.

* `shr_arith`: the low words and the top word shifted arithmetically by 59.
* `mred_arith`: `k m` added to the low words, then the carry into the top
  word, and the top word's sign and its carry into the word above.
-/

@[expose] public section

namespace VG.Proof.Divstep.WordArith

/-- `L + M X` modulo `M K`, for `L < M`. -/
theorem mod_split {L M X K : Nat} (hL : L < M) : (L + M * X) % (M * K) = L + M * (X % K) := by
  have e : L + M * X = L + M * (X % K) + M * K * (X / K) := by
    have := Nat.mod_add_div X K
    have : M * X = M * (X % K) + M * K * (X / K) := by
      rw [Nat.mul_assoc, ← Nat.mul_add, this]
    omega_using [this]
  rw [e, Nat.add_mul_mod_self_left]
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK; simp
  · apply Nat.mod_eq_of_lt
    have := Nat.mod_lt X hK
    have : M * (X % K) + M ≤ M * K := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ this
    omega_using [hL, this]

/-- The value of `ν + 1` words is at least half their range exactly when
their top word is. -/
theorem half_top {Wlo A : Nat} (x : Nat) (hW : Wlo < A) :
    (A * 2 ^ 63 ≤ Wlo + A * x) ↔ 2 ^ 63 ≤ x := by
  constructor
  · intro h
    refine Nat.le_of_not_lt fun hx => ?_
    have : A * (x + 1) ≤ A * 2 ^ 63 := Nat.mul_le_mul_left A hx
    rw [Nat.mul_add_one] at this; omega_using [hW, h, this]
  · intro h; have := Nat.mul_le_mul_left A h; omega_using [this]

/-- A shift by 59: the low words `L` (shifted, with the top word's low bits
shifted in) and `y`, the top word `x` shifted arithmetically by 59, are
`shr_nat`'s `(V + 2 H (2^64 - 1 if V ≥ H)) / 2^59 mod 2 H`. -/
theorem shr_arith {L Vlo M x y : Nat} (hx : x < 2 ^ 64) (hVlo : Vlo < M)
    (hy : y = if 2 ^ 63 ≤ x then x / 2 ^ 59 + 2 ^ 64 - 2 ^ 5 else x / 2 ^ 59)
    (hL : L + M * (x / 2 ^ 59) = (Vlo + M * x) / 2 ^ 59) (hLM : L < M) :
    L + M * y =
      (Vlo + M * x + 2 * (M * 2 ^ 63) * (if M * 2 ^ 63 ≤ Vlo + M * x then 2 ^ 64 - 1 else 0)) /
        2 ^ 59 % (2 * (M * 2 ^ 63)) := by
  subst hy
  have e2 : 2 * (M * 2 ^ 63) = M * 2 ^ 64 := by rw [show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from rfl]; ac_rfl
  by_cases hneg : 2 ^ 63 ≤ x
  · have hc : M * 2 ^ 63 ≤ Vlo + M * x := by
      have := Nat.mul_le_mul_left M hneg; omega_using [this]
    rw [ite_eq_left hneg, ite_eq_left hc, e2]
    have e3 : M * 2 ^ 64 * (2 ^ 64 - 1) = 2 ^ 59 * (M * (2 ^ 5 * (2 ^ 64 - 1))) := by
      rw [show (2 : Nat) ^ 64 = 2 ^ 59 * 2 ^ 5 from rfl]; ac_rfl
    rw [e3, Nat.add_mul_div_left _ _ (Nat.two_pow_pos 59), ← hL, Nat.add_assoc, ← Nat.mul_add, mod_split hLM]
    have inner : (x / 2 ^ 59 + 2 ^ 5 * (2 ^ 64 - 1)) % 2 ^ 64 = x / 2 ^ 59 + 2 ^ 64 - 2 ^ 5 := by
      omega_using [hx]
    rw [inner]
  · have hc : ¬ M * 2 ^ 63 ≤ Vlo + M * x := by
      have : M * (x + 1) ≤ M * 2 ^ 63 := Nat.mul_le_mul_left M (by omega_using [hneg])
      rw [Nat.mul_add_one] at this; omega_using [hVlo, this]
    rw [ite_eq_right hneg, ite_eq_right hc, Nat.mul_zero, Nat.add_zero, e2, ← hL, mod_split hLM,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)]

/-- The top of a Montgomery reduction. `k m` added to the low words `Wlo`
gives `L` and the carry `c` (`hmac`). The top word `top` plus `c` is `lo`,
with its carry `cy`. The sign of `top`, all ones or zero, plus `cy` is `hi`.
Together they are `mredRaw_nat`'s `E`, `ν + 2` words of `t + k m` with `t`'s
sign extended. -/
theorem mred_arith {L Wlo P k A top c lo hi : Nat} (ht : top < 2 ^ 64) (hc : c < 2 ^ 64)
    (hWlo : Wlo < A) (hL : L < A) (hmac : L + A * c = Wlo + k * P)
    (hlo : lo = (top + c) % 2 ^ 64)
    (hhi : hi = ((if 2 ^ 63 ≤ top then 2 ^ 64 - 1 else 0) + (top + c) / 2 ^ 64) % 2 ^ 64) :
    L + A * lo + A * 2 ^ 64 * hi =
      (Wlo + A * top + A * 2 ^ 64 * (if A * 2 ^ 63 ≤ Wlo + A * top then 2 ^ 64 - 1 else 0) + k * P) %
        (A * 2 ^ 64 * 2 ^ 64) := by
  subst hlo hhi
  simp only [half_top _ hWlo]
  generalize hS : (if 2 ^ 63 ≤ top then 2 ^ 64 - 1 else 0) = Sv
  have hSv : Sv = 0 ∨ Sv = 2 ^ 64 - 1 := by rw [← hS]; split <;> simp
  have hr : Wlo + A * top + A * 2 ^ 64 * Sv + k * P = L + A * (top + c + 2 ^ 64 * Sv) := by
    rw [Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc]; omega
  have inner : (top + c) % 2 ^ 64 + 2 ^ 64 * ((Sv + (top + c) / 2 ^ 64) % 2 ^ 64) =
      (top + c + 2 ^ 64 * Sv) % (2 ^ 64 * 2 ^ 64) := by
    rcases hSv with h | h <;> subst h <;> omega
  rw [hr, Nat.mul_assoc A (2 ^ 64) (2 ^ 64), mod_split hL, ← inner, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

end VG.Proof.Divstep.WordArith
