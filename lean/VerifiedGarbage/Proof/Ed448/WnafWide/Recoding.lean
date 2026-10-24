module

public import VerifiedGarbage.Impl.Ed448.WnafWide
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.SplitIfs

/-! Exact public recoding, including carry beyond the unreduced 456-bit input. -/

@[expose] public section

namespace VG.Proof.Ed448.WnafWide

open VG.Impl.Ed448.WnafWide

private theorem pow2_eq (n:Nat) : pow2 n=2^n:=rfl

theorem step (wide : Bool) (k : Nat) :
    (k : Int) = 2 * (next wide k : Int) + digit wide k := by
  cases wide <;> simp only [next, digit, half, radix, Bool.false_eq_true,
    ↓reduceIte, Nat.reduceMul] <;> split_ifs <;> omega

theorem digit_bounds (wide : Bool) (k : Nat) :
    -(half wide : Int) < digit wide k ∧ digit wide k < half wide := by
  cases wide <;> simp only [digit, half, radix, Bool.false_eq_true,
    ↓reduceIte, Nat.reduceMul] <;> split_ifs <;> omega

theorem next_bound (wide : Bool) (k : Nat) : next wide k ≤ k / 2 + half wide / 2 := by
  cases wide <;> simp only [next, half, radix, Bool.false_eq_true,
    ↓reduceIte, Nat.reduceMul, Nat.reduceDiv] <;> split_ifs <;> omega

theorem next_small : ∀ (wide : Bool), ∀ k ≤ half wide, residual wide k 8 = 0 := by
  decide +kernel

theorem residual_add (wide : Bool) (k a b : Nat) :
    residual wide k (a + b) = residual wide (residual wide k a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change next wide (residual wide k (a + b)) = next wide (residual wide (residual wide k a) b)
    rw [ih]

theorem residual_bound (wide : Bool) (k n : Nat) :
    residual wide k n ≤ k / 2 ^ n + half wide := by
  induction n with
  | zero => simp only [residual, Nat.pow_zero, Nat.div_one]; omega
  | succ n ih =>
    have hn := next_bound wide (residual wide k n)
    rw [residual, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    cases wide <;> simp only [half, Bool.false_eq_true, ↓reduceIte] at * <;> omega

/-- Eight carry positions suffice even when the challenge is not reduced modulo L. -/
theorem residual_end (wide : Bool) {k : Nat} (hk : k < scalarLimit) : residual wide k 464 = 0 := by
  rw [scalarLimit,pow2_eq] at hk
  have hb := residual_bound wide k 456
  rw [Nat.div_eq_of_lt hk, Nat.zero_add] at hb
  change residual wide k (456 + 8) = 0
  rw [residual_add]
  exact next_small wide _ hb

theorem tail_quotient {k i:Nat} (hk:k<scalarLimit) (hi:456≤i) : k/2^i=0:=by
  rw [scalarLimit,pow2_eq] at hk
  exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hk
    (Nat.pow_le_pow_right (n:=2) (i:=456) (j:=i) Nat.zero_lt_two hi))

theorem digit_mod (wide : Bool) (k : Nat) : digit wide (k % radix wide) = digit wide k := by
  have h : k % radix wide % 2 = k % 2 := by
    cases wide <;> simp only [radix, half, Bool.false_eq_true,
      ↓reduceIte, Nat.reduceMul] <;> omega
  simp only [digit, h, Nat.mod_mod]

theorem local_digit (wide : Bool) {q h c : Nat} (hc : q + half wide = h + c) :
    localDigit wide (h % radix wide) c = digit wide q := by
  have he : (h % radix wide + c + half wide) % radix wide = q % radix wide := by
    cases wide <;> simp only [radix, half, Bool.false_eq_true,
      ↓reduceIte, Nat.reduceMul] at * <;> omega
  rw [localDigit, he, digit_mod]

theorem carry_bounds (wide : Bool) {bits c : Nat} (hc : c ≤ radix wide) :
    carryNext wide bits c ≤ radix wide := by
  have hd := digit_bounds wide ((bits + c + half wide) % radix wide)
  unfold carryNext localDigit
  cases wide <;> simp only [radix, half, Bool.false_eq_true,
    ↓reduceIte, Nat.reduceMul] at * <;> omega

theorem carry_step (wide : Bool) {q h c : Nat} (hc : q + half wide = h + c) :
    next wide q + half wide = h / 2 + carryNext wide (h % radix wide) c := by
  have hd := digit_bounds wide q
  have hs := step wide q
  have he : h % radix wide % 2 = h % 2 := by
    cases wide <;> simp only [radix, half, Bool.false_eq_true,
      ↓reduceIte, Nat.reduceMul] <;> omega
  unfold carryNext
  rw [local_digit wide hc, he]
  have hn : (0 : Int) ≤ (h % 2 : Nat) + c + half wide - digit wide q := by omega
  have ht := Int.toNat_of_nonneg hn
  omega

private theorem odd_small : ∀ (wide : Bool), ∀ k<radix wide,
    digit wide k=0 ∨ (digit wide k).natAbs%2=1 := by decide +kernel

theorem digit_zero_or_odd (wide : Bool) (k : Nat) :
    digit wide k=0 ∨ (digit wide k).natAbs%2=1 := by
  rw [←digit_mod wide k]
  exact odd_small wide _ (Nat.mod_lt _ (by cases wide <;> decide))

theorem residual_step (wide : Bool) (k n : Nat) :
    (residual wide k n : Int)=2*(residual wide k (n+1) : Int)+digitAt wide k n := step wide _

end VG.Proof.Ed448.WnafWide
