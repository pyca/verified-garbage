module
-- separate module: its lemmas name no ISA, for any target's batched inverse over 64-bit words
public import VerifiedGarbage.Proof.Divstep.TcS
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef

import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Rsa.Divstep.OddInput
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Inversion by batches of divsteps: signed coefficients, any odd modulus

`invRunS`'s bounds for a modulus `p ≥ 1` (not only `p > 1`) and an input up
to any `M ≥ p` (`invRunS_bounds`): what a loop of batches needs at each
batch. And its result after `B` batches that finish the divsteps
(`invRunS_done`): `g = 0`, `|f| = gcd(p, u)` and `u (± a) 2^((64 - N) B) ≡ |f|`
modulo `p` (`+` for `f ≥ 0`), from the odd input `oddInput p u` that adds
`p` to an even `u`.
-/

@[expose] public section

namespace VG.Proof.Divstep

/-- `a`, `b` stay in `(-p, 2p)`, for any `p > 0`. -/
theorem invRunS_range_pos {N : Nat} (hN : N ≤ 62) {p m x : Int} (hp0 : 0 < p) (hm : (p * m + 1) % 2 ^ 64 = 0) :
    ∀ B, -p < (invRunS N p m x B).a ∧ (invRunS N p m x B).a < 2 * p ∧
      -p < (invRunS N p m x B).b ∧ (invRunS N p m x B).b < 2 * p
  | 0 => by simp only [invRunS]; omega_arith
  | B + 1 => by
    obtain ⟨a0, a1, b0, b1⟩ := invRunS_range_pos (x := x) hN hp0 hm B
    obtain ⟨bu, bq⟩ := msteps_bnd (invRunS N p m x B).d (invRunS N p m x B).f (invRunS N p m x B).g N
    have ha : |(invRunS N p m x B).a| ≤ 2 * p := abs_le.mpr ⟨by omega_arith, by omega_arith⟩
    have hb : |(invRunS N p m x B).b| ≤ 2 * p := abs_le.mpr ⟨by omega_arith, by omega_arith⟩
    have rA := mredRaw_range hp0 hm (comb_le2 hN hp0 bu ha hb)
    have rB := mredRaw_range hp0 hm (comb_le2 hN hp0 bq ha hb)
    simp only [invRunS, batchS]
    exact ⟨rA.1, rA.2, rB.1, rB.2⟩

/-- The bounds at every batch, for an input `0 ≤ x ≤ M` and `p ≤ M`. -/
theorem invRunS_bounds {N : Nat} (hN : N ≤ 62) {p m x M : Int} (hp : p % 2 = 1) (hp0 : 0 < p)
    (hm : (p * m + 1) % 2 ^ 64 = 0) (hx0 : 0 ≤ x) (hpM : p ≤ M) (hxM : x ≤ M) (B : Nat) :
    |(invRunS N p m x B).d| ≤ 1 + 2 * (N * B : Nat) ∧ (invRunS N p m x B).f % 2 = 1 ∧
      |(invRunS N p m x B).f| ≤ M ∧ |(invRunS N p m x B).g| ≤ M ∧
      -p < (invRunS N p m x B).a ∧ (invRunS N p m x B).a < 2 * p ∧
      -p < (invRunS N p m x B).b ∧ (invRunS N p m x B).b < 2 * p := by
  obtain ⟨rd, rf, rg, -, -⟩ := invRunS_rel (N := N) (x := x) hp hp0 hm B
  obtain ⟨hd, hodd⟩ := invRun_dfg (N := N) (m := m) (x := x) hp B
  have e1 : (invRun N p m x B).d = (divsteps (N * B) (1, p, x)).1 := by rw [← hd]
  have e2 : (invRun N p m x B).f = (divsteps (N * B) (1, p, x)).2.1 := by rw [← hd]
  have e3 : (invRun N p m x B).g = (divsteps (N * B) (1, p, x)).2.2 := by rw [← hd]
  obtain ⟨lf, lg⟩ := divsteps_le (M := M) (d := 1) (f := p) (g := x) (by decide) hp
    (by rw [abs_of_pos hp0]; exact hpM) (by rw [abs_of_nonneg hx0]; exact hxM) (N * B)
  have ld := divsteps_d (1, p, x) (N * B)
  obtain ⟨a0, a1, b0, b1⟩ := invRunS_range_pos (x := x) hN hp0 hm B
  refine ⟨?_, by rw [rf]; exact hodd, by rw [rf, e2]; exact lf, by rw [rg, e3]; exact lg, a0, a1, b0, b1⟩
  rw [rd, e1]; simpa using ld

/-- After `B` batches that finish the divsteps of `(1, p, oddInput p u)`: `g = 0`,
`|f| = gcd(p, u)`, and `u (± a) 2^((64 - N) B) ≡ |f|` modulo `p`. -/
theorem invRunS_done {N B : Nat} (hN : N ≤ 62) {p m u : Nat} (hp : p % 2 = 1)
    (hm : ((p : Int) * m + 1) % 2 ^ 64 = 0)
    (hdone : (divsteps (N * B) (1, (p : Int), (Rsa.Divstep.oddInput p u : Int))).2.2 = 0 ∧
      (divsteps (N * B) (1, (p : Int), (Rsa.Divstep.oddInput p u : Int))).2.1.natAbs = Nat.gcd p u) :
    (invRunS N p m (Rsa.Divstep.oddInput p u) B).g = 0 ∧
      (invRunS N p m (Rsa.Divstep.oddInput p u) B).f.natAbs = Nat.gcd p u ∧
      (u : Int) * ((if 0 ≤ (invRunS N p m (Rsa.Divstep.oddInput p u) B).f then 1 else -1) *
        (invRunS N p m (Rsa.Divstep.oddInput p u) B).a) * 2 ^ ((64 - N) * B) ≡
        (Nat.gcd p u : Int) [ZMOD p] := by
  have hp0 : (0 : Int) < p := by omega_arith
  have hpo : (p : Int) % 2 = 1 := by exact_mod_cast hp
  set x : Int := (Rsa.Divstep.oddInput p u : Int) with hx
  obtain ⟨rd, rf, rg, ra, -⟩ := invRunS_rel (N := N) (x := x) hpo hp0 hm B
  obtain ⟨hd, -⟩ := invRun_dfg (N := N) (m := (m : Int)) (x := x) hpo B
  have e2 : (invRun N p m x B).f = (divsteps (N * B) (1, (p : Int), x)).2.1 := by rw [← hd]
  have e3 : (invRun N p m x B).g = (divsteps (N * B) (1, (p : Int), x)).2.2 := by rw [← hd]
  have hg : (invRunS N p m x B).g = 0 := by rw [rg, e3]; exact hdone.1
  have hf : (invRunS N p m x B).f.natAbs = Nat.gcd p u := by rw [rf, e2]; exact hdone.2
  refine ⟨hg, hf, ?_⟩
  rcases Nat.lt_or_ge 1 p with hp1 | hp1
  · have hI := (invRun_inv (x := x) hN hpo (by exact_mod_cast hp1) hm B).1
    -- `f ≡ x a K` for the signed run's `a` too.
    have hS : (invRunS N p m x B).f ≡ x * (invRunS N p m x B).a * 2 ^ ((64 - N) * B) [ZMOD p] := by
      rw [rf]; exact hI.trans ((ra.symm.mul_left x).mul_right _)
    have hxu : x ≡ (u : Int) [ZMOD p] := by
      rw [hx]; unfold Rsa.Divstep.oddInput
      split
      · push_cast; exact Int.modEq_iff_dvd.mpr ⟨-1, by omega⟩
      · rw [Nat.add_zero]
    have hS' : (invRunS N p m x B).f ≡ (u : Int) * (invRunS N p m x B).a * 2 ^ ((64 - N) * B) [ZMOD p] :=
      hS.trans ((hxu.mul_right _).mul_right _)
    have habs : ((Nat.gcd p u : Nat) : Int) = |(invRunS N p m x B).f| := by
      rw [← hf, Int.natCast_natAbs]
    rw [habs]
    split
    · rename_i h0
      rw [abs_of_nonneg h0, one_mul]; exact hS'.symm
    · rename_i h0
      rw [abs_of_neg (by omega_arith)]
      have := hS'.neg
      have e : -((u : Int) * (invRunS N p m x B).a * 2 ^ ((64 - N) * B)) =
          (u : Int) * (-1 * (invRunS N p m x B).a) * 2 ^ ((64 - N) * B) := by ring
      rw [e] at this
      exact this.symm
  · have h1 : (p : Int) = 1 := by omega_arith
    rw [h1]; exact Int.modEq_one

end VG.Proof.Divstep
