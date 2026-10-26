module

import VerifiedGarbage.Proof.Divstep.Iter
public import VerifiedGarbage.Proof.Divstep.Bound
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-! # Uniform divstep convergence for RSA-sized operands

An odd second input may exceed the modulus: its first divstep swaps the
operands into the existing convergence cone. Adding the odd modulus to an
even input makes this applicable without a preliminary division.
-/

@[expose] public section

namespace VG.Proof.Rsa.Divstep
open VG.Proof.Divstep

/-- A uniform contraction bound, independent of the RSA values. -/
theorem contraction_words (w : Nat) (hw : 0<w) :
    (2 : ℚ)^(32*w)*s^(80*w) ≤ fuzz := by
  have base : (2 : ℚ)^32*s^80 ≤ fuzz := pow_fuzz (by decide +kernel)
  have fuzz1 : fuzz ≤ (1 : ℚ) := by unfold fuzz; norm_num
  let r : ℚ := 2^32*s^80
  have hr : 0≤r := by dsimp [r]; positivity
  have r1 : r≤1 := base.trans fuzz1
  have step : ∀ k : Nat, r^(k+1)≤r := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc r^(k+1+1)=r^(k+1)*r := by rw [pow_succ]
           _ ≤ r^(k+1)*1 := mul_le_mul_of_nonneg_left r1 (pow_nonneg hr _)
           _ = r^(k+1) := by simp
           _ ≤ r := ih
  rw [pow_mul, pow_mul, ← mul_pow]
  have := step (w-1)
  rw [show w-1+1=w by omega] at this
  exact this.trans base

/-- Odd inputs need no preliminary division even when the second is larger.
A first swap puts the larger-input case back in the existing convergence cone. -/
theorem done_words {w steps : Nat} {p x : Int} (hw : 0<w)
    (hp : p%2=1) (hp0 : 0≤p) (hx0 : 0≤x)
    (start : x≤p ∨ x%2=1)
    (hpSize : p≤2^(32*w)) (hxSize : x≤2^(32*w)) (hn : 80*w+1≤steps) :
    (divsteps steps (1,p,x)).2.2=0 ∧
      (divsteps steps (1,p,x)).2.1.natAbs=Int.gcd p x := by
  have zero : (divsteps steps (1,p,x)).2.2=0 := by
    by_cases le : x≤p
    · exact (divsteps_bound hp hx0 le hpSize (contraction_words w hw) (by omega : 80*w≤steps)).1
    · have odd : x%2=1 := start.resolve_left le
      have first : divsteps 1 (1,p,x)=(1,x,(x-p)/2) := by
        simp [divsteps,divstep,odd]
      rw [show steps=1+(steps-1) by omega,divsteps_add,first]
      exact (divsteps_bound odd (by omega) (by omega) hxSize (contraction_words w hw)
        (by omega : 80*w≤steps-1)).1
  refine ⟨zero,?_⟩
  have h := divsteps_gcd (d:=1) (f:=p) (g:=x) (by decide) hp steps
  rw [zero,Int.gcd_zero_right] at h
  exact h

end VG.Proof.Rsa.Divstep
