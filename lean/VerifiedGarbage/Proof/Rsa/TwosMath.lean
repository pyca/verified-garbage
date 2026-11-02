module

public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Basic
import Mathlib.Data.Prod.Basic
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Push
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
import Mathlib.Basic.IsEmpty.Defs

/-!
# Halvings, windows and rows on naturals

Target-independent models, on naturals, of fixed numbers of steps:

* Halvings of `m`, each only if `m` is even, counting them
  (`halveStep`): as many as `m` has bits leave `splitTwos m` (`halve_iter`).
* A window of an exponent's bits (`window_split`), and a row of a product
  (`row_alg`).
-/

@[expose] public section

namespace VG.Proof.Rsa

open VG.Spec.Rsa (splitTwos powMod)
open VG.Proof.Bignum (mont_cancel)

/-! ## Halvings -/

/-- `(m, t) ↦ (m / 2, t + 1)` if `m` is even. -/
def halveStep (st : Nat × Nat) : Nat × Nat := if st.1 % 2 = 0 then (st.1 / 2, st.2 + 1) else st

theorem splitTwos_odd {m : Nat} (h : m % 2 = 1) : splitTwos m = (0, m) := by
  rw [Spec.Rsa.splitTwos.eq_1]; simp [h]

theorem splitTwos_even {m : Nat} (h0 : m ≠ 0) (h : m % 2 = 0) :
    splitTwos m = ((splitTwos (m / 2)).1 + 1, (splitTwos (m / 2)).2) := by
  have h' : ¬ (m = 0 ∨ m % 2 = 1) := by omega
  rw [Spec.Rsa.splitTwos.eq_1]; simp only [h', ite_false]

/-- `m = 2^t r` with `r` odd. -/
theorem splitTwos_spec {m : Nat} (hm : 0 < m) :
    m = 2 ^ (splitTwos m).1 * (splitTwos m).2 ∧ (splitTwos m).2 % 2 = 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · obtain ⟨e1, e2⟩ := ih (m / 2) (by omega) (by omega)
      rw [splitTwos_even (by omega) h]
      refine ⟨?_, e2⟩
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ _) 2, Nat.mul_assoc, ← e1]
      omega
    · rw [splitTwos_odd h]
      exact ⟨by simp, h⟩

theorem splitTwos_lt {m K : Nat} (hm : 0 < m) (hK : m < 2 ^ K) : (splitTwos m).1 < K := by
  obtain ⟨e1, e2⟩ := splitTwos_spec hm
  have h1 : 2 ^ (splitTwos m).1 ≤ m :=
    calc 2 ^ (splitTwos m).1 ≤ 2 ^ (splitTwos m).1 * (splitTwos m).2 := Nat.le_mul_of_pos_right _ (by omega)
      _ = m := e1.symm
  exact (Nat.pow_lt_pow_iff_right (by decide)).mp (Nat.lt_of_le_of_lt h1 hK)

/-- At least `t` halvings of `m = 2^t r` leave `(r, s + t)`. -/
theorem halve_iter {m : Nat} (hm : 0 < m) {K : Nat} (hK : (splitTwos m).1 ≤ K) (s : Nat) :
    halveStep^[K] (m, s) = ((splitTwos m).2, s + (splitTwos m).1) := by
  induction K generalizing m s with
  | zero =>
    have h0 : (splitTwos m).1 = 0 := by omega
    have hodd : m % 2 = 1 := by
      have := (splitTwos_spec hm).1; rw [h0, Nat.pow_zero, Nat.one_mul] at this
      have := (splitTwos_spec hm).2; omega
    rw [splitTwos_odd hodd]; rfl
  | succ K ih =>
    rw [Function.iterate_succ_apply]
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · have e := splitTwos_even (by omega) h
      have hs : halveStep (m, s) = (m / 2, s + 1) := by simp [halveStep, h]
      rw [hs, ih (by omega) (by rw [e] at hK; dsimp only at hK; omega), e]
      simp only [Prod.mk.injEq, true_and]
      omega
    · have hs : halveStep (m, s) = (m, s) := by simp [halveStep, h]
      rw [hs, ih hm (by rw [splitTwos_odd h]; exact Nat.zero_le _), splitTwos_odd h]

/-- `K` halvings of `0 < m < 2^K`, from `t = 0`: `splitTwos m`, swapped. -/
theorem halve_done {m K : Nat} (hm : 0 < m) (hK : m < 2 ^ K) :
    halveStep^[K] (m, 0) = ((splitTwos m).2, (splitTwos m).1) := by
  rw [halve_iter hm (Nat.le_of_lt (splitTwos_lt hm hK)), Nat.zero_add]

/-! ## Arithmetic of the code

What the implementations' proofs use about the numbers they compute: a
product by rows, and the windows of an exponent's bits. -/

/-- A number below `P R` of the form `A + P (W + Q H)` with `R ≤ Q`: `H = 0`
and `W < R`. -/
theorem window_split {T A W H P Q R : Nat} (hT : T = A + P * (W + Q * H)) (hlt : T < P * R) (hRQ : R ≤ Q) :
    H = 0 ∧ W < R := by
  have h1 : P * (W + Q * H) < P * R := Nat.lt_of_le_of_lt (by rw [hT]; exact Nat.le_add_left _ _) hlt
  have h2 : W + Q * H < R := Nat.lt_of_mul_lt_mul_left h1
  refine ⟨?_, by omega⟩
  rcases Nat.eq_zero_or_pos H with h | h
  · exact h
  · have : Q ≤ Q * H := Nat.le_mul_of_pos_right _ h
    omega

theorem row_alg {A P W c D Ej Q : Nat} (hT : D * Ej = A + P * (W + Q * 0)) :
    A + P * (W + c * D + Q * 0) = D * (Ej + P * c) := by
  grind

end VG.Proof.Rsa
