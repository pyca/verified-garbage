module
-- separate module: its lemmas name no ISA, so any target's batched inverse of 59-step batches can import them

public import VerifiedGarbage.Proof.Divstep.TcS
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef
import VerifiedGarbage.Proof.Divstep.Alg
import VerifiedGarbage.Proof.Rsa.Divstep.Bound
import VerifiedGarbage.Proof.Rsa.Divstep.OddInput
import VerifiedGarbage.Proof.Rsa.Divstep.Batch64
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring

/-! # The result of a batched inverse of 59-step batches

After `3 n + 2` batches of `invRunS 59` (64-bit Montgomery reductions) from
`(1, p, oddInput p x)` for an odd `p > 1` of `n` words: `g = 0`,
`|f| = gcd(p, x)`, and any `r ≡ ±a (mod p)` (the sign of `f`) times
`2^(5 (3 n + 2))` modulo `p` is a coefficient `y < p` with
`p ∣ y x - gcd(p, x)` (`invRunS59_result`). The 64-bit counterpart of
`InvResult.lean`'s; independent of any ISA.
-/

@[expose] public section

namespace VG.Proof.Rsa.Divstep
open VG.Proof.Divstep

theorem oddInput_cong64 (p x : Nat) : (oddInput p x : Int) ≡ x [ZMOD (p : Int)] := by
  unfold oddInput
  split_ifs <;> simp [Int.ModEq, Nat.cast_add]

/-- After `3 n + 2` batches of 59 divsteps: `g = 0`, `|f| = gcd(p, x)`, and
`p ∣ ((r 2^(5 (3 n + 2))) mod p) x - gcd(p, x)` for `r ≡ ±a (mod p)`, `a`
negated if `f < 0`. -/
theorem invRunS59_result {p x mi n : Nat} (odd : p % 2 = 1) (large : 1 < p)
    (hm : ((p : Int) * mi + 1) % 2 ^ 64 = 0) (pc : p < 2 ^ (64 * n)) (xc : x < 2 ^ (64 * n)) :
    (invRunS 59 p mi (oddInput p x) (3 * n + 2)).g = 0 ∧
    (invRunS 59 p mi (oddInput p x) (3 * n + 2)).f.natAbs = Nat.gcd p x ∧
    ∀ r : Nat, (r : Int) ≡ (if (invRunS 59 p mi (oddInput p x) (3 * n + 2)).f < 0 then
        -(invRunS 59 p mi (oddInput p x) (3 * n + 2)).a else (invRunS 59 p mi (oddInput p x) (3 * n + 2)).a)
        [ZMOD (p : Int)] →
      (p : Int) ∣ ((r * 2 ^ (5 * (3 * n + 2)) % p : Nat) : Int) * x - (Nat.gcd p x : Int) := by
  set B := 3 * n + 2
  set st := invRunS 59 p mi (oddInput p x) B
  have io : (p : Int) % 2 = 1 := by exact_mod_cast odd
  have pi : (0 : Int) < p := by exact_mod_cast (by omega : 0 < p)
  obtain ⟨rd, rf, rg⟩ := invRunS_dfg' (N := 59) (p := (p : Int)) (m := (mi : Int)) (x := (oddInput p x : Int)) B
  obtain ⟨dfg, -⟩ := invRun_dfg (N := 59) (m := (mi : Int)) (x := (oddInput p x : Int)) io B
  have x1 : x < 2 ^ (32 * (2 * n + 1)) := by
    have : 2 ^ (64 * n) ≤ 2 ^ (32 * (2 * n + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hxo := oddInput_lt (m := p) (x := x) (R := 2 ^ (64 * n)) pc xc
  have done := done_words (w := 2 * n + 1) (steps := 59 * B) (p := (p : Int)) (x := (oddInput p x : Int))
    (by omega) io (by omega) (by omega) (Or.inr (by exact_mod_cast oddInput_odd (x := x) odd))
    (by
      have : 2 ^ (64 * n) ≤ 2 ^ (32 * (2 * n + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      exact_mod_cast (by omega : p ≤ 2 ^ (32 * (2 * n + 1))))
    (by
      have : 2 * 2 ^ (64 * n) ≤ 2 ^ (32 * (2 * n + 1)) := by
        rw [show 32 * (2 * n + 1) = 64 * n + 32 by omega, Nat.pow_add, Nat.mul_comm 2]
        exact Nat.mul_le_mul_left _ (by decide : 2 ≤ 2 ^ 32)
      exact_mod_cast (by omega : oddInput p x ≤ 2 ^ (32 * (2 * n + 1))))
    (by omega)
  rw [← dfg] at done
  simp only at done
  rw [← rf, ← rg] at done
  have hg : Int.gcd (p : Int) (oddInput p x : Int) = Nat.gcd p x := by
    rw [Int.gcd_natCast_natCast, oddInput_gcd]
  refine ⟨done.1, by rw [done.2, hg], fun r hr => ?_⟩
  -- `f ≡ x a 2^(5 B)`.
  obtain ⟨-, -, -, ha, -⟩ := invRunS_rel (N := 59) (x := (oddInput p x : Int)) io pi hm B
  have inv := invRun_inv (N := 59) (x := (oddInput p x : Int)) (by decide) io (by exact_mod_cast large) hm B
  have e5 : (64 - 59) * B = 5 * B := rfl
  rw [e5] at inv
  have hf : st.f ≡ (oddInput p x : Int) * st.a * 2 ^ (5 * B) [ZMOD (p : Int)] := by
    rw [rf]; exact inv.1.trans ((ha.symm.mul_left _).mul_right _)
  have habs : (|st.f| : Int) ≡ (oddInput p x : Int) * (if st.f < 0 then -st.a else st.a) * 2 ^ (5 * B)
      [ZMOD (p : Int)] := by
    by_cases h : st.f < 0
    · rw [abs_of_neg h, ite_eq_left h]
      have := hf.neg
      rw [show (oddInput p x : Int) * -st.a * 2 ^ (5 * B) = -((oddInput p x : Int) * st.a * 2 ^ (5 * B)) by ring]
      exact this
    · rw [abs_of_nonneg (by omega), ite_eq_right h]; exact hf
  have hv : (|st.f| : Int) = (Nat.gcd p x : Int) := by
    rw [← Int.natCast_natAbs, done.2, hg]
  rw [hv] at habs
  have hy : (((r * 2 ^ (5 * B) % p : Nat) : Int)) ≡ (r : Int) * 2 ^ (5 * B) [ZMOD (p : Int)] := by
    rw [Int.natCast_emod]; push_cast; exact Int.mod_modEq _ _
  have key : (((r * 2 ^ (5 * B) % p : Nat) : Int)) * x ≡ (Nat.gcd p x : Int) [ZMOD (p : Int)] := by
    refine ((hy.mul_right _).trans ?_).trans habs.symm
    have := ((hr.mul_right (2 ^ (5 * B))).mul_right (x : Int)).trans
      (((oddInput_cong64 p x).symm.mul_left _))
    calc (r : Int) * 2 ^ (5 * B) * x ≡ (if st.f < 0 then -st.a else st.a) * 2 ^ (5 * B) * (oddInput p x : Int)
          [ZMOD (p : Int)] := this
      _ = (oddInput p x : Int) * (if st.f < 0 then -st.a else st.a) * 2 ^ (5 * B) := by ring
  exact (Int.ModEq.dvd key.symm)

end VG.Proof.Rsa.Divstep
