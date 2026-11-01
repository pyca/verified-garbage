module

public import VerifiedGarbage.Proof.Divstep.TcS
public import VerifiedGarbage.Proof.Divstep.BatchBasic
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Divstep.Batch
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# A batch of 59 divsteps on 64-bit words, for RSA-sized operands

What code running `invRunS 59` (`Proof/Divstep/TcS.lean`) on numbers of
`n + 1` words needs of the state before batch `k` and its matrix
(`batch64`): `f` odd, `d` small enough for the packed divsteps, `f`, `g` no
larger than their start (below `2^(64 n + 1)`), `a`, `b` in `(-p, 2p)`, the
matrix's rows of sum at most `2^59`, and the next state from them.
-/

@[expose] public section

namespace VG.Proof.Rsa.Divstep
open VG.Proof.Divstep

/-- `d` grows by at most `2` a divstep. -/
theorem invRunS_d {p m x : Int} : ∀ k, |(invRunS 59 p m x k).d| ≤ 1 + 118 * k
  | 0 => by simp [invRunS]
  | k + 1 => by
    have := invRunS_d (p := p) (m := m) (x := x) k
    have h := msteps_d (MSt.init (invRunS 59 p m x k).d (invRunS 59 p m x k).f (invRunS 59 p m x k).g) 59
    simp only [invRunS, batchS, MSt.init] at h ⊢
    push_cast at this h ⊢
    linarith

theorem batch64 {n k : Nat} {p m x : Int} (hp : p % 2 = 1) (hp1 : 1 < p) (hm : (p * m + 1) % 2 ^ 64 = 0)
    (hx : 0 ≤ x) (hpC : p < 2 ^ (64 * n + 1)) (hxC : x < 2 ^ (64 * n + 1)) (hd : 1 + 118 * k ≤ 2 ^ 30) :
    (invRunS 59 p m x k).f % 2 = 1 ∧ |(invRunS 59 p m x k).d| ≤ 2 ^ 30 ∧
    |(invRunS 59 p m x k).f| < 2 ^ (64 * n + 1) ∧ |(invRunS 59 p m x k).g| < 2 ^ (64 * n + 1) ∧
    (-p < (invRunS 59 p m x k).a ∧ (invRunS 59 p m x k).a < 2 * p ∧
      -p < (invRunS 59 p m x k).b ∧ (invRunS 59 p m x k).b < 2 * p) ∧
    |(msteps 59 (MSt.init (invRunS 59 p m x k).d (invRunS 59 p m x k).f (invRunS 59 p m x k).g)).u| +
      |(msteps 59 (MSt.init (invRunS 59 p m x k).d (invRunS 59 p m x k).f (invRunS 59 p m x k).g)).v| ≤ 2 ^ 59 ∧
    |(msteps 59 (MSt.init (invRunS 59 p m x k).d (invRunS 59 p m x k).f (invRunS 59 p m x k).g)).q| +
      |(msteps 59 (MSt.init (invRunS 59 p m x k).d (invRunS 59 p m x k).f (invRunS 59 p m x k).g)).r| ≤ 2 ^ 59 ∧
    (msteps 59 (MSt.init (invRunS 59 p m x k).d (invRunS 59 p m x k).f (invRunS 59 p m x k).g)).u *
        (invRunS 59 p m x k).f +
      (msteps 59 (MSt.init (invRunS 59 p m x k).d (invRunS 59 p m x k).f (invRunS 59 p m x k).g)).v *
        (invRunS 59 p m x k).g = 2 ^ 59 * (invRunS 59 p m x (k + 1)).f ∧
    (msteps 59 (MSt.init (invRunS 59 p m x k).d (invRunS 59 p m x k).f (invRunS 59 p m x k).g)).q *
        (invRunS 59 p m x k).f +
      (msteps 59 (MSt.init (invRunS 59 p m x k).d (invRunS 59 p m x k).f (invRunS 59 p m x k).g)).r *
        (invRunS 59 p m x k).g = 2 ^ 59 * (invRunS 59 p m x (k + 1)).g ∧
    (invRunS 59 p m x (k + 1)).a = mredRaw p m
      ((msteps 59 (MSt.init (invRunS 59 p m x k).d (invRunS 59 p m x k).f (invRunS 59 p m x k).g)).u *
        (invRunS 59 p m x k).a +
       (msteps 59 (MSt.init (invRunS 59 p m x k).d (invRunS 59 p m x k).f (invRunS 59 p m x k).g)).v *
        (invRunS 59 p m x k).b) ∧
    (invRunS 59 p m x (k + 1)).b = mredRaw p m
      ((msteps 59 (MSt.init (invRunS 59 p m x k).d (invRunS 59 p m x k).f (invRunS 59 p m x k).g)).q *
        (invRunS 59 p m x k).a +
       (msteps 59 (MSt.init (invRunS 59 p m x k).d (invRunS 59 p m x k).f (invRunS 59 p m x k).g)).r *
        (invRunS 59 p m x k).b) ∧
    (invRunS 59 p m x (k + 1)).d =
      (msteps 59 (MSt.init (invRunS 59 p m x k).d (invRunS 59 p m x k).f (invRunS 59 p m x k).g)).d := by
  set s := invRunS 59 p m x k with hs
  set t := msteps 59 (MSt.init s.d s.f s.g) with ht
  obtain ⟨rd, rf, rg, -, -⟩ := invRunS_rel (N := 59) (x := x) hp (by omega) hm k
  obtain ⟨dfg, fodd⟩ := invRun_dfg (N := 59) (m := m) (x := x) hp k
  have hf : s.f % 2 = 1 := by rw [rf]; exact fodd
  -- `|f|, |g|` stay below the start's bound.
  have hle := divsteps_le (M := 2 ^ (64 * n + 1) - 1) (d := 1) (f := p) (g := x) (by decide) hp
    (by rw [abs_of_nonneg (by omega)]; omega) (by rw [abs_of_nonneg hx]; omega) (59 * k)
  rw [← dfg] at hle
  simp only at hle
  rw [← rf, ← rg] at hle
  obtain ⟨bu, bq⟩ := msteps_bnd s.d s.f s.g 59
  obtain ⟨m1, m2⟩ := msteps_mat (d := s.d) (g := s.g) hf 59
  have hd' := invRunS_d (p := p) (m := m) (x := x) k
  have hpos : (0 : Int) < 2 ^ 59 := by decide
  refine ⟨hf, hd'.trans (by exact_mod_cast hd), by linarith [hle.1], by linarith [hle.2],
    invRunS_range (x := x) (by decide) hp1 hm k, bu, bq, ?_, ?_, by simp only [invRunS, batchS, hs, ht], by simp only [invRunS, batchS, hs, ht],
    by simp only [invRunS, batchS, hs, ht]⟩
  · show t.u * s.f + t.v * s.g = 2 ^ 59 * ((t.u * s.f + t.v * s.g) / 2 ^ 59)
    rw [← m1, Int.mul_ediv_cancel_left _ hpos.ne']
  · show t.q * s.f + t.r * s.g = 2 ^ 59 * ((t.q * s.f + t.r * s.g) / 2 ^ 59)
    rw [← m2, Int.mul_ediv_cancel_left _ hpos.ne']

/-- A matrix row on numbers below `M` in magnitude. -/
theorem comb_bound {u v f g M : Int} (hu : |u| + |v| ≤ 2 ^ 59) (hf : |f| ≤ M) (hg : |g| ≤ M) :
    |u * f + v * g| ≤ 2 ^ 59 * M := by
  have h1 : |u * f| ≤ |u| * M := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hf (abs_nonneg _)
  have h2 : |v * g| ≤ |v| * M := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hg (abs_nonneg _)
  have hM : 0 ≤ M := le_trans (abs_nonneg _) hf
  calc |u * f + v * g| ≤ |u * f| + |v * g| := abs_add_le _ _
    _ ≤ |u| * M + |v| * M := add_le_add h1 h2
    _ = (|u| + |v|) * M := (add_mul _ _ _).symm
    _ ≤ 2 ^ 59 * M := mul_le_mul_of_nonneg_right hu hM

/-- A matrix row's entries, which fit in a signed word. -/
theorem row_parts {u v : Int} (h : |u| + |v| ≤ 2 ^ 59) :
    -2 ^ 59 ≤ u ∧ u ≤ 2 ^ 59 ∧ -2 ^ 59 ≤ v ∧ v ≤ 2 ^ 59 ∧ u.natAbs + v.natAbs ≤ 2 ^ 62 := by
  have a := abs_le.mp (show |u| ≤ 2 ^ 59 by linarith [abs_nonneg v])
  have b := abs_le.mp (show |v| ≤ 2 ^ 59 by linarith [abs_nonneg u])
  have cu := Int.natCast_natAbs u
  have cv := Int.natCast_natAbs v
  refine ⟨a.1, a.2, b.1, b.2, ?_⟩
  have : ((u.natAbs + v.natAbs : Nat) : Int) ≤ 2 ^ 62 := by push_cast; linarith
  exact_mod_cast this

/-- `|f| < M` as two inequalities. -/
theorem abs_lt_parts {f M : Int} (h : |f| < M) : -M < f ∧ f < M := abs_lt.mp h

/-- A matrix row on numbers below `2^(64 n + 1)` fits in `n + 1` signed words. -/
theorem comb_range {u v f g : Int} {n : Nat} (huv : |u| + |v| ≤ 2 ^ 59) (hf : |f| < 2 ^ (64 * n + 1))
    (hg : |g| < 2 ^ (64 * n + 1)) :
    -2 ^ (64 * (n + 1) - 1) ≤ u * f + v * g ∧ u * f + v * g < 2 ^ (64 * (n + 1) - 1) := by
  have h := comb_bound huv hf.le hg.le
  have e : (2 : Int) ^ (64 * (n + 1) - 1) = 2 ^ 59 * 2 ^ (64 * n + 1) * 8 := by
    rw [show 64 * (n + 1) - 1 = 59 + (64 * n + 1) + 3 by omega, pow_add, pow_add]; norm_num
  have hp : (0 : Int) < 2 ^ 59 * 2 ^ (64 * n + 1) := by positivity
  rw [e]
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor <;> linarith

/-- `(-p, 2p)` for `p < 2^(64 n)`: below `2^(64 n + 1)` in magnitude, and in
`n + 1` signed words. -/
theorem range_parts {a : Int} {p n : Nat} (h : -(p : Int) < a ∧ a < 2 * p) (hp : p < 2 ^ (64 * n)) :
    |a| < 2 ^ (64 * n + 1) ∧ -2 ^ (64 * (n + 1) - 1) ≤ a ∧ a < 2 ^ (64 * (n + 1) - 1) := by
  have hp' : (p : Int) < 2 ^ (64 * n) := by exact_mod_cast hp
  have e1 : (2 : Int) ^ (64 * n + 1) = 2 * 2 ^ (64 * n) := by rw [pow_succ, mul_comm]
  have e2 : (2 : Int) ^ (64 * (n + 1) - 1) = 2 ^ 63 * 2 ^ (64 * n) := by
    rw [show 64 * (n + 1) - 1 = 63 + 64 * n by omega, pow_add]
  have hP : (0 : Int) < 2 ^ (64 * n) := by positivity
  refine ⟨abs_lt.mpr ⟨by rw [e1]; linarith, by rw [e1]; linarith⟩, ?_, ?_⟩ <;> rw [e2] <;> linarith

end VG.Proof.Rsa.Divstep
