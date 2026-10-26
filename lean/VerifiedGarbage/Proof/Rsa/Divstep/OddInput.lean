module
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef

import VerifiedGarbage.Proof.Rsa.Divstep.Bound
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Proof.Divstep.Steps
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-! # Making a divstep input odd without division -/

@[expose] public section
namespace VG.Proof.Rsa.Divstep
open VG.Proof.Divstep


theorem oddInput_odd {m x : Nat} (hm : m % 2 = 1) : oddInput m x % 2 = 1 := by
  unfold oddInput
  split_ifs <;> omega

theorem oddInput_gcd (m x : Nat) : Nat.gcd m (oddInput m x) = Nat.gcd m x := by
  unfold oddInput
  split_ifs
  · exact Nat.gcd_add_self_right m x
  · simp

theorem oddInput_lt {m x R : Nat} (hm : m < R) (hx : x < R) : oddInput m x < 2 * R := by
  unfold oddInput
  split_ifs <;> omega

theorem oddInput_done {m x n : Nat} (hm : m % 2 = 1)
    (hmR : m < 2 ^ (32*n)) (hxR : x < 2 ^ (32*n)) :
    (divsteps (30*(3*(n+1))) (1,m,oddInput m x)).2.2 = 0 ∧
      (divsteps (30*(3*(n+1))) (1,m,oddInput m x)).2.1.natAbs = Nat.gcd m x := by
  have grow : 2 * 2 ^ (32*n) ≤ 2 ^ (32*(n+1)) := by
    rw [show 32*(n+1)=32*n+32 by omega, pow_add]
    have : 2 ≤ 2 ^ (32 : Nat) := by decide
    nlinarith [Nat.two_pow_pos (32*n)]
  have h := done_words (w:=n+1) (steps:=30*(3*(n+1))) (by omega)
    (by exact_mod_cast hm) (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    (Or.inr (by exact_mod_cast oddInput_odd (x:=x) hm))
    (by exact_mod_cast (hmR.le.trans (by omega : 2 ^ (32*n) ≤ 2 ^ (32*(n+1)))))
    (by exact_mod_cast ((oddInput_lt hmR hxR).le.trans grow)) (by omega)
  rw [Int.gcd_natCast_natCast,oddInput_gcd] at h
  exact h

end VG.Proof.Rsa.Divstep
