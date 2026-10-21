module

public import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Tactic.Conv
import Mathlib.Data.Nat.Basic

/-! Single-pass binary exponentiation and root detection. A set bit starts
another possible trailing-zero chain, discarding the previous result. -/

@[expose] public section
namespace VG.Proof.Rsa.Fused

structure State where
  value : Nat
  root : Option Nat
  done : Bool
  deriving DecidableEq, Repr

def start (n y : Nat) : State := ⟨y, none, decide (y = 1 ∨ y = n - 1)⟩

def step (n b : Nat) (bit : Bool) (s : State) : State :=
  let x := s.value * s.value % n
  if bit then start n (x * b % n) else
    ⟨x, if !s.done && decide (x = 1) then some s.value else s.root,
      s.done || decide (x = 1 ∨ x = n - 1)⟩

def zeros (n : Nat) : Nat → State → State
  | 0, s => s
  | k + 1, s => zeros n k (step n 0 false s)

theorem zeros_done {n : Nat} {s : State} (h : s.done = true) (k : Nat) :
    (zeros n k s).root = s.root := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [zeros, ih (by simp [step, h])]
    simp [step, h]

theorem zeros_start_stop {n y : Nat} (h : y = 1 ∨ y = n - 1) (k : Nat) :
    (zeros n k (start n y)).root = none :=
  zeros_done (by simp [start, h]) k

/-- This includes the specification's behavior on invalid keys. -/
theorem zeros_search (n y k : Nat) :
    (zeros n (k + 1) ⟨y, none, false⟩).root =
      Spec.Rsa.recoverStep.squarings n k y := by
  induction k generalizing y with
  | zero =>
    simp only [zeros, step, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.true_and, Bool.false_or, Spec.Rsa.recoverStep.squarings]
    by_cases h : y * y % n = 1 <;> simp [h]
  | succ k ih =>
    rw [zeros]
    by_cases h1 : y * y % n = 1
    · have hs : step n 0 false ⟨y, none, false⟩ = ⟨y * y % n, some y, true⟩ := by
        simp [step, h1]
      rw [hs, zeros_done rfl]
      simp [Spec.Rsa.recoverStep.squarings, h1]
    · by_cases h2 : y * y % n = n - 1
      · have hs : step n 0 false ⟨y, none, false⟩ = ⟨y * y % n, none, true⟩ := by
          simp only [step, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and, h1, decide_false, Bool.false_or]
          simp [h2]
        rw [hs, zeros_done rfl]
        simp only [Spec.Rsa.recoverStep.squarings, h1, ↓reduceIte]
        simp [h2]
      · have hs : step n 0 false ⟨y, none, false⟩ = ⟨y * y % n, none, false⟩ := by
          simp [step, h1, h2]
        rw [hs, ih]
        simp [Spec.Rsa.recoverStep.squarings, h1, h2]

theorem zeros_result (n b r t : Nat) (ht : 0 < t) :
    (zeros n t (start n (Spec.Rsa.powMod b r n))).root =
      Spec.Rsa.recoverStep n t r b := by
  unfold Spec.Rsa.recoverStep
  by_cases stop : Spec.Rsa.powMod b r n = 1 ∨ Spec.Rsa.powMod b r n = n - 1
  · rw [ite_eq_left stop, zeros_start_stop stop]
  · rw [ite_eq_right stop]
    have hs : start n (Spec.Rsa.powMod b r n) = ⟨Spec.Rsa.powMod b r n, none, false⟩ := by
      simp [start, stop]
    rw [hs, show t = (t - 1) + 1 by omega, zeros_search]
    congr 1 <;> omega

def bits (n b : Nat) : Nat → Nat → State → State
  | 0, _, s => s
  | k + 1, e, s => bits n b k e (step n b (decide (e / 2 ^ k % 2 = 1)) s)

def eval (n b e : Nat) : State :=
  if e = 0 then start n 1 else
    step n b (decide (e % 2 = 1)) (eval n b (e / 2))
termination_by e

theorem eval_zero (n b : Nat) : eval n b 0 = start n 1 := by
  rw [eval]; simp

theorem eval_value (n b e : Nat) (hn : 1 < n) : (eval n b e).value = b ^ e % n := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    rw [eval]
    split
    · rename_i h; subst h; simp [start, Nat.mod_eq_of_lt hn]
    · rename_i h
      have val := ih (e / 2) (by omega)
      have exp : e = e / 2 * 2 + e % 2 := by have := Nat.div_add_mod e 2; omega
      have power : b ^ e % n = ((b ^ (e / 2) % n) * (b ^ (e / 2) % n) * b ^ (e % 2)) % n := by
        conv_lhs => rw [exp, Nat.pow_add, Nat.pow_mul, Nat.pow_two]
        simp only [Nat.mul_mod, Nat.mod_mod]
      rw [power]
      rcases Nat.mod_two_eq_zero_or_one e with even | odd
      · simp [step, even, val, Nat.mul_mod]
      · simp [step, odd, start, val, Nat.mul_mod]

theorem eval_step (n b e : Nat) (hn : 1 < n) :
    step n b (decide (e % 2 = 1)) (eval n b (e / 2)) = eval n b e := by
  by_cases he : e = 0
  · subst he; rw [eval_zero]; simp [step, start, Nat.mod_eq_of_lt hn]
  · exact (show eval n b e = _ from by rw [eval, ite_eq_right he]).symm

theorem bits_eval (n b e k : Nat) (hn : 1 < n) :
    bits n b k e (eval n b (e / 2 ^ k)) = eval n b e := by
  induction k with
  | zero => simp [bits]
  | succ k ih =>
    rw [bits]
    have div : e / 2 ^ (k + 1) = (e / 2 ^ k) / 2 := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    rw [div, eval_step n b _ hn]
    exact ih

theorem zeros_succ_last (n k : Nat) (s : State) :
    zeros n (k + 1) s = step n 0 false (zeros n k s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact ih _

theorem eval_odd (n b r : Nat) (hn : 1 < n) (hr : r % 2 = 1) :
    eval n b r = start n (Spec.Rsa.powMod b r n) := by
  have rp : r ≠ 0 := by omega
  rw [eval, ite_eq_right rp, show decide (r % 2 = 1) = true by simp [hr]]
  unfold step
  simp only [↓reduceIte]
  congr 1
  have value := eval_value n b r hn
  rw [eval, ite_eq_right rp] at value
  simpa only [step, hr, decide_true, ↓reduceIte, start, VG.Proof.Bignum.powMod_eq] using value

theorem eval_zeros (n b r t : Nat) (hr : 0 < r) :
    eval n b (r * 2 ^ t) = zeros n t (eval n b r) := by
  induction t with
  | zero => simp [zeros]
  | succ t ih =>
    have p : 0 < r * 2 ^ t := Nat.mul_pos hr (Nat.two_pow_pos _)
    have even : r * 2 ^ (t + 1) % 2 = 0 := by rw [Nat.pow_succ, ← Nat.mul_assoc]; omega
    have div : r * 2 ^ (t + 1) / 2 = r * 2 ^ t := by rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by decide)]
    rw [eval, ite_eq_right (by omega), even, div, ih, zeros_succ_last]
    rfl

/-- The full fixed-width pass has exactly the specified result. -/
theorem result (n b e c : Nat) (hn : 1 < n) (he : 0 < e) (bound : e < 2 ^ c)
    (even : e % 2 = 0) :
    (bits n b c e (start n 1)).root =
      Spec.Rsa.recoverStep n (Spec.Rsa.splitTwos e).1 (Spec.Rsa.splitTwos e).2 b := by
  obtain ⟨split, odd⟩ := VG.Proof.Rsa.splitTwos_spec he
  have rpos : 0 < (Spec.Rsa.splitTwos e).2 := by omega
  have tpos : 0 < (Spec.Rsa.splitTwos e).1 := by
    by_contra h
    have zero : (Spec.Rsa.splitTwos e).1 = 0 := by omega
    simp only [zero, Nat.pow_zero, Nat.one_mul] at split
    omega
  have initial : start n 1 = eval n b (e / 2 ^ c) := by
    rw [Nat.div_eq_of_lt bound, eval_zero]
  rw [initial, bits_eval n b e c hn]
  conv_lhs => rw [split, Nat.mul_comm]
  rw [eval_zeros n b _ _ rpos, eval_odd n b _ hn odd, zeros_result n b _ _ tpos]

theorem step_flags (n b : Nat) (bit : Bool) (s : State) :
    let x := s.value*s.value%n
    let next := step n b bit s
    next.done = (((s.done || decide (x=1) || decide (x=n-1)) && !bit) ||
      ((decide (next.value=1) || decide (next.value=n-1)) && bit)) ∧
    next.root.isSome = ((s.root.isSome || (!s.done && decide (x=1) && !bit)) && !bit) := by
  cases bit
  · simp only [step, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.and_true,
      Bool.and_false, Bool.or_false]
    refine ⟨by simp [Bool.or_assoc], ?_⟩
    cases h : (!s.done && decide (s.value*s.value%n=1)) <;> simp
  · simp [step,start]

theorem step_value (n b : Nat) (bit : Bool) (s : State) :
    (step n b bit s).value = if bit then s.value*s.value%n*b%n else s.value*s.value%n := by
  cases bit <;> rfl

theorem step_root (n b : Nat) (bit : Bool) (s : State) :
    (step n b bit s).root = if bit then none else
      if !s.done && decide (s.value*s.value%n=1) then some s.value else s.root := by
  cases bit <;> rfl

theorem step_lt (n b : Nat) (bit : Bool) (s : State) (hn : 0<n) :
    (step n b bit s).value<n := by
  rw [step_value]
  split <;> exact Nat.mod_lt _ hn

theorem four_eval (n b q w : Nat) (hn : 1<n) (hw : w<16) :
    bits n b 4 w (eval n b q) = eval n b (q*16+w) := by
  have e := bits_eval n b (q*16+w) 4 hn
  have div : (q*16+w)/2^4=q := by change (q*16+w)/16=q; omega
  rw [div] at e
  have b3 : (q*16+w)/2^3%2=w/2^3%2 := by change (q*16+w)/8%2=w/8%2; omega
  have b2 : (q*16+w)/2^2%2=w/2^2%2 := by change (q*16+w)/4%2=w/4%2; omega
  have b1 : (q*16+w)/2^1%2=w/2^1%2 := by change (q*16+w)/2%2=w/2%2; omega
  have b0 : (q*16+w)/2^0%2=w/2^0%2 := by change (q*16+w)/1%2=w/1%2; omega
  simpa only [bits,b3,b2,b1,b0] using e

theorem eval_result (n b e c : Nat) (hn : 1<n) (he : 0<e) (fit : e<2^c) (even : e%2=0) :
    (eval n b e).root=Spec.Rsa.recoverStep n (Spec.Rsa.splitTwos e).1 (Spec.Rsa.splitTwos e).2 b := by
  have r := result n b e c hn he fit even
  have init : start n 1=eval n b (e/2^c) := by rw [Nat.div_eq_of_lt fit,eval_zero]
  rw [init,bits_eval n b e c hn] at r
  exact r

end VG.Proof.Rsa.Fused
