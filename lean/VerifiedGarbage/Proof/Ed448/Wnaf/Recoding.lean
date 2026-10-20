module

public import VerifiedGarbage.Impl.Ed448.Wnaf
public import VerifiedGarbage.Proof.Framework.PowLit
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Omega

/-! Exact recoding, including the carry beyond bit 455. -/

@[expose] public section

namespace VG.Proof.Ed448.Wnaf

open VG.Impl.Ed448.Wnaf

theorem step (k : Nat) : (k : Int) = 2 * (next k : Int) + digit k := by
  have h32 : k = 32 * (k / 32) + k % 32 := by omega
  have h2 : k = 2 * (k / 2) + k % 2 := by omega
  unfold next digit
  split
  · omega
  · split
    · have : (k + 16) / 32 = k / 32 := by omega
      rw [this]
      omega
    · have : (k + 16) / 32 = k / 32 + 1 := by omega
      rw [this]
      omega

theorem digit_bounds (k : Nat) : -15 ≤ digit k ∧ digit k ≤ 15 := by
  have h : k % 32 % 2 = k % 2 := by omega
  unfold digit
  split_ifs <;> omega

theorem next_bound (k : Nat) : next k ≤ k / 2 + 8 := by
  unfold next
  split <;> omega

theorem next_small : ∀ k ≤ 16, residual k 5 = 0 := by decide +kernel

theorem next_zero : next 0 = 0 := rfl

theorem residual_add (k a b : Nat) : residual k (a + b) = residual (residual k a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change next (residual k (a + b)) = next (residual (residual k a) b)
    rw [ih]

/-- The rounding error stays bounded, independent of the input size. -/
theorem residual_bound (k n : Nat) : residual k n ≤ k / 2 ^ n + 16 := by
  induction n with
  | zero => simp only [residual, pow_zero, Nat.div_one]; omega
  | succ n ih =>
    have hn := next_bound (residual k n)
    rw [residual, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    omega

/-- Five carry positions suffice for every unreduced 456-bit input. -/
theorem residual_end {k : Nat} (hk : k < 2 ^ 456) : residual k 461 = 0 := by
  have hb := residual_bound k 456
  rw [Nat.div_eq_of_lt hk, Nat.zero_add] at hb
  change residual k (456 + 5) = 0
  rw [residual_add]
  exact next_small _ hb

theorem residual_step (k n : Nat) :
    (residual k n : Int) = 2 * (residual k (n + 1) : Int) + digitAt k n := step _

theorem digit_mod (k : Nat) : digit (k % 32) = digit k := by
  have h : k % 32 % 2 = k % 2 := by omega
  simp only [digit, h, Nat.mod_mod]

theorem local_digit {q h c : Nat} (hc : q + 16 = h + c) :
    localDigit (h % 32) c = digit q := by
  have he : (h % 32 + c + 16) % 32 = q % 32 := by omega
  rw [localDigit, he, digit_mod]

theorem carry_bounds : ∀ bits < 32, ∀ c ≤ 32, carryNext bits c ≤ 32 := by decide +kernel

/-- One finite carry update agrees with the unbounded integer recoding. -/
theorem carry_step {q h c : Nat} (hc : q + 16 = h + c) (hbound : c ≤ 32) :
    next q + 16 = h / 2 + carryNext (h % 32) c := by
  have hd := digit_bounds q
  have hs := step q
  have he : h % 32 % 2 = h % 2 := by omega
  unfold carryNext
  rw [local_digit hc, he]
  have hn : (0 : Int) ≤ (h % 2 : Nat) + c + 16 - digit q := by omega
  have ht := Int.toNat_of_nonneg hn
  omega

end VG.Proof.Ed448.Wnaf
