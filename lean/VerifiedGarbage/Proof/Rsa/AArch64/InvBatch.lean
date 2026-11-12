module

import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega

public import VerifiedGarbage.Proof.Divstep.SignedWords
public import VerifiedGarbage.Proof.Divstep.Alg
public import VerifiedGarbage.Proof.Divstep.TcS
import VerifiedGarbage.Proof.Divstep.TcSBounds
public import VerifiedGarbage.Proof.Divstep.BatchBasic
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Impl.Rsa.AArch64.Keys
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
public import VerifiedGarbage.Proof.Bignum.AArch64.Csub
public import VerifiedGarbage.Proof.Rsa.Ranges
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
public import VerifiedGarbage.Proof.Rsa.AArch64.Div
public import VerifiedGarbage.Proof.Rsa.AArch64.InvLaw
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Divstep.Batch
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import VerifiedGarbage.Proof.Rsa.Divstep.Bound
import VerifiedGarbage.Proof.Rsa.Divstep.OddInput
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.Divstep.RowWord
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvPacked
public import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Data.Int.GCD

/-!
# RSA private keys on AArch64: the batched inverse's proof

The proof of `Keys.inverse` (`inverse_ok`) and the instance of its contract
(`InvLaw`) the registrations use. One module: everything here imports the
divstep algebra (`Proof/Divstep/Alg`, `Tc`, `Packed`), whose importers
`ci/check_lean_speed.py` counts. In order: signed Montgomery words, the
facts of a batch of 59 divsteps and the result of `3 n + 2` of them (none
names an ISA), then the code's loops, a batch, the start, the end, the
contract and the instance.
-/

@[expose] public section

-- From `Proof/Divstep/MredWords.lean`.
/-!
# Signed multiword numbers modulo `2^(64 L)`

Signed numbers of `L` words modulo `2^(64 L)` (`sgn_emod`, `sgn_of_emod`), and
a signed number's low word (`sgn_mod64`).
-/


namespace VG.Proof.Divstep

theorem pow64_cast (L : Nat) : ((2 ^ (64 * L) : Nat) : Int) = 2 ^ (64 * L) := by push_cast; rfl

/-- `2^(64 L)` and `2^(64 L - 1)` through `H`. -/
theorem pow_H {L : Nat} (hL : 1 ≤ L) : ∃ H : Nat, 2 ^ 63 ≤ H ∧ 2 ^ (64 * L - 1) = H ∧ 2 ^ (64 * L) = 2 * H ∧
    (2 : Int) ^ (64 * L - 1) = H ∧ (2 : Int) ^ (64 * L) = 2 * H := by
  obtain ⟨e, h63⟩ := pow_half hL
  refine ⟨_, h63, rfl, e, by push_cast; rfl, ?_⟩
  rw [← pow64_cast, e]; push_cast; rfl

/-- A signed number is its words modulo `2^(64 L)`. -/
theorem sgn_emod {L x : Nat} (hL : 1 ≤ L) (hx : x < 2 ^ (64 * L)) : sgn L x % 2 ^ (64 * L) = x := by
  obtain ⟨H, h63, e1, e2, e3, e4⟩ := pow_H hL
  unfold sgn
  simp only [e1, e4]; rw [e2] at hx
  split
  · exact Int.emod_eq_of_lt (by omega_arith) (by omega_arith)
  · rw [show (x : Int) - 2 * H = x + (-1) * (2 * H) by omega_arith, Int.add_mul_emod_self_right]
    exact Int.emod_eq_of_lt (by omega_arith) (by omega_arith)

/-- The signed number of `L` words congruent to `y`, if `y` fits. -/
theorem sgn_of_emod {L x : Nat} {y : Int} (hL : 1 ≤ L)
    (hy₀ : -2 ^ (64 * L - 1) ≤ y) (hy₁ : y < 2 ^ (64 * L - 1)) (h : (x : Int) = y % 2 ^ (64 * L)) :
    sgn L x = y := by
  obtain ⟨H, h63, e1, e2, e3, e4⟩ := pow_H hL
  unfold sgn
  simp only [e1, e4]; rw [e3] at hy₀ hy₁; rw [e4] at h
  by_cases hy : 0 ≤ y
  · rw [Int.emod_eq_of_lt hy (by omega_arith)] at h
    rw [ite_eq_left (by omega_arith : x < H)]; exact h
  · rw [show y = (y + 2 * H) + (-1) * (2 * H) by omega_arith, Int.add_mul_emod_self_right,
      Int.emod_eq_of_lt (by omega_arith) (by omega_arith)] at h
    rw [ite_eq_right (by omega_arith : ¬ x < H)]; omega_arith

/-- A signed number's low word. -/
theorem sgn_mod64 {L F : Nat} (hL : 1 ≤ L) (hF : F < 2 ^ (64 * L)) : sgn L F % 2 ^ 64 = ((F % 2 ^ 64 : Nat) : Int) := by
  have e := Int.emod_add_mul_ediv (sgn L F) (2 ^ (64 * L))
  rw [sgn_emod hL hF] at e
  have hd : (2 : Int) ^ 64 ∣ 2 ^ (64 * L) := ⟨2 ^ (64 * L - 64), by rw [← Int.pow_add]; congr 1; omega_arith⟩
  rw [← e, Int.add_emod, Int.emod_eq_zero_of_dvd (Int.dvd_mul_of_dvd_left hd), Int.add_zero, Int.emod_emod]
  rfl

/-- A word's signed value is a small integer's. -/
theorem toInt_ofInt64 {u : Int} (h0 : -2 ^ 63 ≤ u) (h1 : u < 2 ^ 63) : (BitVec.ofInt 64 u).toInt = u := by
  rw [BitVec.toInt_ofInt]; exact Int.bmod_eq_of_le (by omega_arith) (by omega_arith)


/-! ## Negating and correcting signed numbers -/

/-- The sign of a number of `n + 1` words is its top word's top bit. -/
theorem sgn_neg_iff {n W s : Nat} (hW : W < 2 ^ (64 * n)) (hs : s < 2 ^ 64) :
    sgn (n + 1) (W + 2 ^ (64 * n) * s) < 0 ↔ 2 ^ 63 ≤ s := by
  have t := top_sign hW hs
  unfold sgn
  have hR : W + 2 ^ (64 * n) * s < 2 ^ (64 * (n + 1)) := by
    have : 2 ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by
      rw [← Nat.pow_add, show 64 * n + 64 = 64 * (n + 1) by omega_arith]
    have := Nat.mul_le_mul_left (2 ^ (64 * n)) (show s + 1 ≤ 2 ^ 64 by omega_arith)
    rw [Nat.mul_add, Nat.mul_one] at this
    omega_arith
  split
  · rename_i h; exact ⟨fun h' => by omega_arith, fun h' => absurd (t.mp h) (by omega_arith)⟩
  · rename_i h
    refine ⟨fun _ => Nat.le_of_not_lt fun h' => h (t.mpr h'), fun _ => ?_⟩
    have : ((W + 2 ^ (64 * n) * s : Nat) : Int) < 2 ^ (64 * (n + 1)) := by exact_mod_cast hR
    omega_arith

/-- `([x] ^ mask) + neg`, `neg` the mask's bit: `[x]` negated if `neg`. -/
theorem sgn_cneg {L X Y c : Nat} {neg : Bool} (hL : 1 ≤ L) (hX : X < 2 ^ (64 * L)) (hY : Y < 2 ^ (64 * L))
    (hr : -2 ^ (64 * L - 1) < sgn L X)
    (h : Y + 2 ^ (64 * L) * c = (if neg then 2 ^ (64 * L) - 1 - X else X) + neg.toNat) :
    sgn L Y = if neg then -sgn L X else sgn L X := by
  obtain ⟨H, h63, e1, e2, e3, e4⟩ := pow_H hL
  rw [e3] at hr
  unfold sgn at hr ⊢
  simp only [e1, e4] at hr ⊢
  rw [e2] at hX hY h
  cases neg
  · simp only [Bool.false_eq_true, ite_false, Bool.toNat_false, Nat.add_zero] at h ⊢
    have hc : c = 0 := by
      rcases Nat.eq_zero_or_pos c with hc | hc
      · exact hc
      · have := Nat.mul_le_mul_left (2 * H) hc; omega_arith
    subst hc
    rw [Nat.mul_zero, Nat.add_zero] at h
    subst h
    rfl
  · simp only [ite_true, Bool.toNat_true] at h ⊢
    by_cases hx : X < H
    · rw [ite_eq_left hx]
      by_cases x0 : X = 0
      · subst x0
        have hc : c = 1 := by
          rcases Nat.lt_or_ge c 2 with hc | hc
          · rcases Nat.lt_or_ge c 1 with hc' | hc'
            · have : c = 0 := by omega_arith
              subst this; omega_arith
            · omega_arith
          · have := Nat.mul_le_mul_left (2 * H) hc; omega_arith
        subst hc
        have : Y = 0 := by omega_arith
        subst this
        rw [ite_eq_left (show (0 : Nat) < H by omega_arith)]; simp
      · have hc : c = 0 := by
          rcases Nat.eq_zero_or_pos c with hc | hc
          · exact hc
          · have := Nat.mul_le_mul_left (2 * H) hc; omega_arith
        subst hc
        rw [ite_eq_right (by omega_arith : ¬ Y < H)]
        push_cast
        omega_arith
    · rw [ite_eq_right hx] at hr ⊢
      have hc : c = 0 := by
        rcases Nat.eq_zero_or_pos c with hc | hc
        · exact hc
        · have := Nat.mul_le_mul_left (2 * H) hc; omega_arith
      subst hc
      rw [ite_eq_left (by omega_arith : Y < H)]
      push_cast at hr ⊢
      omega_arith

/-- `[x] += p` modulo `2^(64 L)` if `[x]` is negative. -/
theorem sgn_addIfNeg {L X Y : Nat} {p : Int} (hL : 1 ≤ L) (hX : X < 2 ^ (64 * L))
    (hY : (Y : Int) = (X + if sgn L X < 0 then p else 0) % 2 ^ (64 * L))
    (r₀ : -2 ^ (64 * L - 1) ≤ sgn L X + if sgn L X < 0 then p else 0)
    (r₁ : sgn L X + (if sgn L X < 0 then p else 0) < 2 ^ (64 * L - 1)) :
    sgn L Y = sgn L X + if sgn L X < 0 then p else 0 := by
  refine sgn_of_emod hL r₀ r₁ ?_
  rw [hY, Int.add_emod, ← sgn_emod hL hX, Int.emod_emod, ← Int.add_emod]

end VG.Proof.Divstep

-- From `Proof/Rsa/Divstep/Batch64.lean`.
/-!
# A batch of 59 divsteps on 64-bit words, for RSA-sized operands

What code running `invRunS 59` (`Proof/Divstep/TcS.lean`) on numbers of
`n + 1` words needs of the state before batch `k` and its matrix
(`batch64`): `f` odd, `d` small enough for the packed divsteps, `f`, `g` no
larger than their start (below `2^(64 n + 1)`), `a`, `b` in `(-p, 2p)`, the
matrix's rows of sum at most `2^59`, and the next state from them.
-/


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

/-- `invRunS`'s `d`, `f`, `g` are `invRun`'s, whatever `m`. -/
theorem invRunS_dfg' {N : Nat} {p m x : Int} : ∀ B, (invRunS N p m x B).d = (invRun N p m x B).d ∧
    (invRunS N p m x B).f = (invRun N p m x B).f ∧ (invRunS N p m x B).g = (invRun N p m x B).g
  | 0 => ⟨rfl, rfl, rfl⟩
  | B + 1 => by
    obtain ⟨hd, hf, hg⟩ := invRunS_dfg' (N := N) (p := p) (m := m) (x := x) B
    simp only [invRunS, invRun, batchS, batch]
    rw [hd, hf, hg]
    exact ⟨rfl, rfl, rfl⟩

/-- The `d`, `f`, `g` half of `batch64`: for any odd `p` and any `m`. -/
theorem batch64fg {n k : Nat} {p m x : Int} (hp : p % 2 = 1) (hp0 : 0 ≤ p)
    (hx : 0 ≤ x) (hpC : p < 2 ^ (64 * n + 1)) (hxC : x < 2 ^ (64 * n + 1)) (hd : 1 + 118 * k ≤ 2 ^ 30) :
    (invRunS 59 p m x k).f % 2 = 1 ∧ |(invRunS 59 p m x k).d| ≤ 2 ^ 30 ∧
    |(invRunS 59 p m x k).f| < 2 ^ (64 * n + 1) ∧ |(invRunS 59 p m x k).g| < 2 ^ (64 * n + 1) ∧
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
    (invRunS 59 p m x (k + 1)).d =
      (msteps 59 (MSt.init (invRunS 59 p m x k).d (invRunS 59 p m x k).f (invRunS 59 p m x k).g)).d := by
  set s := invRunS 59 p m x k with hs
  set t := msteps 59 (MSt.init s.d s.f s.g) with ht
  obtain ⟨rd, rf, rg⟩ := invRunS_dfg' (N := 59) (p := p) (m := m) (x := x) k
  obtain ⟨dfg, fodd⟩ := invRun_dfg (N := 59) (m := m) (x := x) hp k
  have hf : s.f % 2 = 1 := by rw [rf]; exact fodd
  -- `|f|, |g|` stay below the start's bound.
  have hle := divsteps_le (M := 2 ^ (64 * n + 1) - 1) (d := 1) (f := p) (g := x) (by decide) hp
    (by rw [abs_of_nonneg hp0]; omega_arith) (by rw [abs_of_nonneg hx]; omega_arith) (59 * k)
  rw [← dfg] at hle
  simp only at hle
  rw [← rf, ← rg] at hle
  obtain ⟨bu, bq⟩ := msteps_bnd s.d s.f s.g 59
  obtain ⟨m1, m2⟩ := msteps_mat (d := s.d) (g := s.g) hf 59
  have hd' := invRunS_d (p := p) (m := m) (x := x) k
  have hpos : (0 : Int) < 2 ^ 59 := by decide
  refine ⟨hf, hd'.trans (by exact_mod_cast hd), by linarith [hle.1], by linarith [hle.2], bu, bq, ?_, ?_,
    by simp only [invRunS, batchS, hs, ht]⟩
  · show t.u * s.f + t.v * s.g = 2 ^ 59 * ((t.u * s.f + t.v * s.g) / 2 ^ 59)
    rw [← m1, Int.mul_ediv_cancel_left _ hpos.ne']
  · show t.q * s.f + t.r * s.g = 2 ^ 59 * ((t.q * s.f + t.r * s.g) / 2 ^ 59)
    rw [← m2, Int.mul_ediv_cancel_left _ hpos.ne']

/-- The `a`, `b` half of `batch64`: for an odd `p > 1` and `m = -p⁻¹`. -/
theorem batch64ab {k : Nat} {p m x : Int} (hp1 : 1 < p) (hm : (p * m + 1) % 2 ^ 64 = 0) :
    (-p < (invRunS 59 p m x k).a ∧ (invRunS 59 p m x k).a < 2 * p ∧
      -p < (invRunS 59 p m x k).b ∧ (invRunS 59 p m x k).b < 2 * p) ∧
    (invRunS 59 p m x (k + 1)).a = mredRaw p m
      ((msteps 59 (MSt.init (invRunS 59 p m x k).d (invRunS 59 p m x k).f (invRunS 59 p m x k).g)).u *
        (invRunS 59 p m x k).a +
       (msteps 59 (MSt.init (invRunS 59 p m x k).d (invRunS 59 p m x k).f (invRunS 59 p m x k).g)).v *
        (invRunS 59 p m x k).b) ∧
    (invRunS 59 p m x (k + 1)).b = mredRaw p m
      ((msteps 59 (MSt.init (invRunS 59 p m x k).d (invRunS 59 p m x k).f (invRunS 59 p m x k).g)).q *
        (invRunS 59 p m x k).a +
       (msteps 59 (MSt.init (invRunS 59 p m x k).d (invRunS 59 p m x k).f (invRunS 59 p m x k).g)).r *
        (invRunS 59 p m x k).b) :=
  ⟨invRunS_range (x := x) (by decide) hp1 hm k, by simp only [invRunS, batchS],
    by simp only [invRunS, batchS]⟩

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

/-- A matrix row on numbers below `2^(64 n + 1)` fits in `n + 1` signed words. -/
theorem comb_range {u v f g : Int} {n : Nat} (huv : |u| + |v| ≤ 2 ^ 59) (hf : |f| < 2 ^ (64 * n + 1))
    (hg : |g| < 2 ^ (64 * n + 1)) :
    -2 ^ (64 * (n + 1) - 1) ≤ u * f + v * g ∧ u * f + v * g < 2 ^ (64 * (n + 1) - 1) := by
  have h := comb_bound huv hf.le hg.le
  have e : (2 : Int) ^ (64 * (n + 1) - 1) = 2 ^ 59 * 2 ^ (64 * n + 1) * 8 := by
    rw [show 64 * (n + 1) - 1 = 59 + (64 * n + 1) + 3 by omega_arith, pow_add, pow_add]; norm_num
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
    rw [show 64 * (n + 1) - 1 = 63 + 64 * n by omega_arith, pow_add]
  have hP : (0 : Int) < 2 ^ (64 * n) := by positivity
  refine ⟨abs_lt.mpr ⟨by rw [e1]; linarith, by rw [e1]; linarith⟩, ?_, ?_⟩ <;> rw [e2] <;> linarith

end VG.Proof.Rsa.Divstep

-- From `Proof/Rsa/Divstep/InvResult64.lean`.
/-! # The result of a batched inverse of 59-step batches

After `3 n + 2` batches of `invRunS 59` (64-bit Montgomery reductions) from
`(1, p, oddInput p x)` for an odd `p > 1` of `n` words: `g = 0`,
`|f| = gcd(p, x)`, and any `r ≡ ±a (mod p)` (the sign of `f`) times
`2^(5 (3 n + 2))` modulo `p` is a coefficient `y < p` with
`p ∣ y x - gcd(p, x)` (`invRunS59_result`). The 64-bit counterpart of
`InvResult.lean`'s; independent of any ISA.
-/


namespace VG.Proof.Rsa.Divstep
open VG.Proof.Divstep

/-- After `3 n + 2` batches of 59 divsteps: `g = 0`, `|f| = gcd(p, x)`, and
`p ∣ ((r 2^(5 (3 n + 2))) mod p) x - gcd(p, x)` for `r ≡ ±a (mod p)`, `a`
negated if `f < 0`: `TcSBounds.lean`'s `invRunS_done`, the run done by
`done_words`. -/
theorem invRunS59_result {p x mi n : Nat} (odd : p % 2 = 1)
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
  have hxo := oddInput_lt (m := p) (x := x) (R := 2 ^ (64 * n)) pc xc
  have done := done_words (w := 2 * n + 1) (steps := 59 * B) (p := (p : Int)) (x := (oddInput p x : Int))
    (by omega_arith) io (by omega_arith) (by omega_arith) (Or.inr (by exact_mod_cast oddInput_odd (x := x) odd))
    (by
      have : 2 ^ (64 * n) ≤ 2 ^ (32 * (2 * n + 1)) := Nat.pow_le_pow_right (by decide) (by omega_arith)
      exact_mod_cast (by omega_arith : p ≤ 2 ^ (32 * (2 * n + 1))))
    (by
      have : 2 * 2 ^ (64 * n) ≤ 2 ^ (32 * (2 * n + 1)) := by
        rw [show 32 * (2 * n + 1) = 64 * n + 32 by omega_arith, Nat.pow_add, Nat.mul_comm 2]
        exact Nat.mul_le_mul_left _ (by decide : 2 ≤ 2 ^ 32)
      exact_mod_cast (by omega_arith : oddInput p x ≤ 2 ^ (32 * (2 * n + 1))))
    (by omega_arith)
  have hg : Int.gcd (p : Int) (oddInput p x : Int) = Nat.gcd p x := by
    rw [Int.gcd_natCast_natCast, oddInput_gcd]
  obtain ⟨g0, f0, cong⟩ := invRunS_done (N := 59) (B := B) (by decide) (m := mi) (u := x) odd hm
    ⟨done.1, by rw [done.2, hg]⟩
  refine ⟨g0, f0, fun r hr => ?_⟩
  have e5 : (64 - 59) * B = 5 * B := rfl
  rw [e5] at cong
  have sgn : (if 0 ≤ st.f then (1 : Int) else -1) * st.a = if st.f < 0 then -st.a else st.a := by
    by_cases h : st.f < 0
    · rw [ite_eq_right (by omega_arith), ite_eq_left h, neg_one_mul]
    · rw [ite_eq_left (by omega_arith), ite_eq_right h, one_mul]
  rw [sgn] at cong
  have hy : (((r * 2 ^ (5 * B) % p : Nat) : Int)) ≡ (r : Int) * 2 ^ (5 * B) [ZMOD (p : Int)] := by
    rw [Int.natCast_emod]; push_cast; exact Int.mod_modEq _ _
  have key : (((r * 2 ^ (5 * B) % p : Nat) : Int)) * x ≡ (Nat.gcd p x : Int) [ZMOD (p : Int)] := by
    refine ((hy.mul_right _).trans ?_).trans cong
    calc (r : Int) * 2 ^ (5 * B) * x ≡ (if st.f < 0 then -st.a else st.a) * 2 ^ (5 * B) * x
          [ZMOD (p : Int)] := (hr.mul_right _).mul_right _
      _ = (x : Int) * (if st.f < 0 then -st.a else st.a) * 2 ^ (5 * B) := by ring
  exact (Int.ModEq.dvd key.symm)

end VG.Proof.Rsa.Divstep

-- From `Proof/Rsa/AArch64/InvFused.lean`.
/-!
# RSA private keys on AArch64: the fused batch's passes

A batch's two passes (`Keys.fgPass`, `Keys.dePass`): each word's two rows at
once (`fgWord_ok`, `deWord_ok`, from `Divstep.rowWord` and, for `k m`,
`kWord`), the loops' invariants (`FgInv`: the words read, shifted, are their
low 59 bits, `2^59` times the words written and the previous sum's top bits;
`DeInv`: the low word, `2^64` times the words written, and the carries), the
top words' signs (`topFixVal`) and the ends (`fgFinal`, `deFinal`): each
output congruent to its value modulo `2^(64 (n + 1))` (`fgPass_ok`,
`dePass_ok`).
-/


namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.InvBatch
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

section
variable {s : State}

theorem exec_sbc_x {d n m : Reg} :
    exec (.sbc .x d n m) s = some (s.write .x d (s.gpr n + ~~~s.gpr m + BitVec.ofNat 64 s.c.toNat)) := rfl

theorem exec_umov_x {d : Reg} {n : VReg} {i : Nat} (h : i < 2) :
    exec (.umov .x d n i) s = some (s.write .x d ((s.v n).extractLsb' (64 * i) 64)) := by
  simp only [exec, Size.bits, show i * 64 < 128 by omega_arith, ite_true]

/-- `movi0`: the vector register cleared. -/
theorem exec_movi0 (r : VReg) : exec (.vop (.movi0 r)) s = some (s.setV r 0) := rfl

end

/-- Code that writes no vector register keeps them all. -/
theorem WP.vfix {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q)
    (hc : c.allInstrs (fun i => (vdstOf i).isNone) = true) :
    WP isa c s fun t => Q t ∧ t.v = s.v := by
  obtain ⟨tr, t, he, hq⟩ := h
  refine ⟨tr, t, he, hq, funext fun r => Exec.vec (fun i hi e => ?_) he⟩
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  have := hc i hi
  rw [e] at this
  exact absurd this (by simp)


theorem mulBitsF_vnone (r : Reg) : ∀ f j, (mulBitsF r f j).all (fun i => (vdstOf i).isNone) = true
  | 0, _ => rfl
  | f + 1, j => by
    rw [mulBitsF]; split
    · rfl
    · simp only [List.all_append, mulBitsF_vnone r f (j / 2)]
      split <;> rfl

theorem base_vnone (j : Nat) (r : Reg) : (base j r).all (fun i => (vdstOf i).isNone) = true := by
  unfold base baseRep mulBits
  split
  · simp only [List.all_append, List.all_replicate]; simp [vdstOf]
  · simp only [List.all_append, mulBitsF_vnone]; rfl

theorem exec_madd_x {s : State} {d n m a : Reg} :
    exec (.madd .x d n m a) s = some (s.write .x d (s.gpr a + s.gpr n * s.gpr m)) := rfl

/-- The sign mask of a coefficient. -/
abbrev Msk (s : State) (m c : Reg) : Prop := s.gpr m = 0#64 - (s.gpr c >>> 63)

/-- A coefficient pair's bound. -/
abbrev Cb (s : State) (c₁ c₂ : Reg) : Prop := (s.gpr c₁).toInt.natAbs + (s.gpr c₂).toInt.natAbs ≤ 2 ^ 62

/-- A word of the pass over `(f, g)`: words `j + 1` of `[x16]`, `[x17]` (at
`eF`, `eG` + 8) read, both rows' sums' words into `x1`, `x24` and on to the
carries, and words `j` written from the previous sums' (`x26`, `x27`). -/
theorem fgWord_ok (s : State) {B : Addr} {Z eF eG : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eF) (h17 : s.gpr .x17 = off B eG) (hF : eF + 16 ≤ Z) (hG : eG + 16 ≤ Z)
    (m9 : Msk s .x9 .x4) (m10 : Msk s .x10 .x5) (m19 : Msk s .x19 .x6) (m20 : Msk s .x20 .x7)
    (b1 : Cb s .x4 .x5) (b2 : Cb s .x6 .x7) (c1 : (s.gpr .x13).toInt.natAbs ≤ 2 ^ 62)
    (c2 : (s.gpr .x25).toInt.natAbs ≤ 2 ^ 62) :
    WP isa (.block fgBody) s fun t => ∃ o₁ o₂ : BitVec 64,
      t.mem = (s.mem.writeW (off B eF) o₁).writeW (off B eG) o₂ ∧
      ((t.gpr .x26).toNat : Int) + 2 ^ 64 * (t.gpr .x13).toInt = (s.gpr .x4).toInt * (word s.mem B (eF + 8)).toNat +
        (s.gpr .x5).toInt * (word s.mem B (eG + 8)).toNat + (s.gpr .x13).toInt ∧
      ((t.gpr .x27).toNat : Int) + 2 ^ 64 * (t.gpr .x25).toInt = (s.gpr .x6).toInt * (word s.mem B (eF + 8)).toNat +
        (s.gpr .x7).toInt * (word s.mem B (eG + 8)).toNat + (s.gpr .x25).toInt ∧
      (t.gpr .x13).toInt.natAbs ≤ 2 ^ 62 ∧ (t.gpr .x25).toInt.natAbs ≤ 2 ^ 62 ∧
      o₁.toNat = (s.gpr .x26).toNat / 2 ^ 59 + 2 ^ 5 * ((t.gpr .x26).toNat % 2 ^ 59) ∧
      o₂.toNat = (s.gpr .x27).toNat / 2 ^ 59 + 2 ^ 5 * ((t.gpr .x27).toNat % 2 ^ 59) ∧
      t.gpr .x16 = off B (eF + 8) ∧ t.gpr .x17 = off B (eG + 8) ∧
      t.gpr .x2 = word s.mem B (eF + 8) ∧ t.gpr .x3 = word s.mem B (eG + 8) := by
  unfold fgBody fgRow prods carryIn
  brun [h16, h17, hs.ld (show eF + 8 + 8 ≤ Z by omega_arith), hs.ld (show eG + 8 + 8 ≤ Z by omega_arith),
    hs.st (show eF + 8 ≤ Z by omega_arith), hs.st (show eG + 8 ≤ Z by omega_arith), exec_sbc_x, exec_extr_x]
  have r1 := Divstep.rowWord (s.gpr .x4) (s.gpr .x5) (word s.mem B (eF + 8)) (word s.mem B (eG + 8)) (s.gpr .x13) b1 c1
  have r2 := Divstep.rowWord (s.gpr .x6) (s.gpr .x7) (word s.mem B (eF + 8)) (word s.mem B (eG + 8)) (s.gpr .x25) b2 c2
  rw [m9, m10, m19, m20]
  simp only [Bool.toNat_false, BitVec.add_zero, Nat.add_zero, word] at r1 r2 ⊢
  exact ⟨_, _, rfl, r1.1, r2.1, r1.2, r2.2, Divstep.extr59 _ _, Divstep.extr59 _ _⟩

/-- `k M + kc` added to `lo + 2^64 c`: its low word into `lo`, the carry out
into `c`, and the high word with the carry of `+ kc` into `kc`. -/
theorem kWord (lo k M kc : BitVec 64) :
    let T := k * M
    let Hk := BitVec.ofNat 64 (k.toNat * M.toNat / 2 ^ 64)
    let T' := T + kc
    let kc' := Hk + BitVec.ofNat 64 (decide (2 ^ 64 ≤ T.toNat + kc.toNat)).toNat
    let lo' := lo + T'
    let C := (decide (2 ^ 64 ≤ lo.toNat + T'.toNat)).toNat
    (lo'.toNat : Int) + 2 ^ 64 * (C + kc'.toNat) = lo.toNat + k.toNat * M.toNat + kc.toNat ∧ C ≤ 1 := by
  intro T Hk T' kc' lo' C
  have hk := k.isLt; have hM := M.isLt; have hkc := kc.isLt; have hl := lo.isLt
  obtain ⟨P, hP⟩ : ∃ P, P = k.toNat * M.toNat := ⟨_, rfl⟩
  have hPq : P / 2 ^ 64 ≤ 2 ^ 64 - 2 := by
    rw [hP]
    have : k.toNat * M.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
    have e : (2 ^ 64 - 1) * (2 ^ 64 - 1) = (2 ^ 64 - 2) * 2 ^ 64 + 1 := by decide
    rw [e] at this
    exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega))
  have hT : T.toNat = P % 2 ^ 64 := by simp only [T, BitVec.toNat_mul, hP]
  have hT' : T'.toNat = (T.toNat + kc.toNat) % 2 ^ 64 := by simp only [T', BitVec.toNat_add]
  have hlo : lo'.toNat = (lo.toNat + T'.toNat) % 2 ^ 64 := by simp only [lo', BitVec.toNat_add]
  have d1 := Divstep.decide_toNat_div (T.toNat + kc.toNat) (by omega)
  have d2 := Divstep.decide_toNat_div (lo.toNat + T'.toNat) (by have := T'.isLt; omega)
  have hkc' : kc'.toNat = P / 2 ^ 64 + (T.toNat + kc.toNat) / 2 ^ 64 := by
    simp only [kc', BitVec.toNat_add, BitVec.toNat_ofNat, d1, Hk, ← hP]
    have : (T.toNat + kc.toNat) / 2 ^ 64 ≤ 1 := by have := T.isLt; omega
    rw [Nat.mod_eq_of_lt (a := P / 2 ^ 64) (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hC : C = (lo.toNat + T'.toNat) / 2 ^ 64 := d2
  have := T'.isLt
  refine ⟨?_, by omega⟩
  rw [hkc', hC, hlo, hT', hT, show ((k.toNat : Int) * M.toNat) = (P : Int) by rw [hP]; push_cast; rfl]
  have := Nat.div_add_mod P (2 ^ 64)
  omega

/-- A carry's bound from its word: `|u X + v Y + c| < 2^123 + 2^61` leaves
`|c'| ≤ 2^59 + 1`. -/
theorem carry_bound {lo : Nat} {c' S : Int} (hlo : lo < 2 ^ 64) (h : (lo : Int) + 2 ^ 64 * c' = S)
    (hS : S.natAbs ≤ 2 ^ 59 * (2 ^ 64 - 1) + 2 ^ 61) : c'.natAbs ≤ 2 ^ 59 + 1 := by
  omega

theorem lin_abs (cu cv : BitVec 64) (X Y : Nat) (c : Int) (hX : X < 2 ^ 64) (hY : Y < 2 ^ 64)
    (hb : cu.toInt.natAbs + cv.toInt.natAbs ≤ 2 ^ 59) (hc : c.natAbs ≤ 2 ^ 61) :
    (cu.toInt * X + cv.toInt * Y + c).natAbs ≤ 2 ^ 59 * (2 ^ 64 - 1) + 2 ^ 61 := by
  have e1 : (cu.toInt * X).natAbs ≤ cu.toInt.natAbs * (2 ^ 64 - 1) := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]; exact Nat.mul_le_mul_left _ (by omega)
  have e2 : (cv.toInt * Y).natAbs ≤ cv.toInt.natAbs * (2 ^ 64 - 1) := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]; exact Nat.mul_le_mul_left _ (by omega)
  have e3 : cu.toInt.natAbs * (2 ^ 64 - 1) + cv.toInt.natAbs * (2 ^ 64 - 1) ≤ 2 ^ 59 * (2 ^ 64 - 1) := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hb
  omega

/-- A coefficient pair's bound for a batch of 59. -/
abbrev Cb59 (s : State) (c₁ c₂ : Reg) : Prop := (s.gpr c₁).toInt.natAbs + (s.gpr c₂).toInt.natAbs ≤ 2 ^ 59

/-- A small signed word plus a carry bit. -/
theorem toInt_add_bit (c : BitVec 64) (C : Nat) (hC : C ≤ 1) (hc : c.toInt.natAbs ≤ 2 ^ 59 + 1) :
    (c + BitVec.ofNat 64 C).toInt = c.toInt + C := by
  rw [BitVec.toInt_add, show (BitVec.ofNat 64 C).toInt = C by
    rcases (show C = 0 ∨ C = 1 by omega) with rfl | rfl <;> decide]
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem natAbs_add_bit {x : Int} {C : Nat} (hC : C ≤ 1) (h : x.natAbs ≤ 2 ^ 59 + 1) :
    (x + C).natAbs ≤ 2 ^ 61 := by
  omega

/-- A row's word over `(a, b)`: `rowWord`, then `k M + kc` (`kWord`), the
carries unmerged. -/
theorem deRowValU (cu cv a b c k M kc : BitVec 64) (hb : cu.toInt.natAbs + cv.toInt.natAbs ≤ 2 ^ 59)
    (hc : c.toInt.natAbs ≤ 2 ^ 61) :
    let lo1 := cu * a
    let hi1 := BitVec.ofNat 64 (cu.toNat * a.toNat / 2 ^ 64) - (a &&& (0#64 - (cu >>> 63)))
    let lo2 := cv * b
    let hi2 := BitVec.ofNat 64 (cv.toNat * b.toNat / 2 ^ 64) - (b &&& (0#64 - (cv >>> 63)))
    let s1 := lo1 + lo2
    let lo := s1 + c
    let c' := hi1 + hi2 + BitVec.ofNat 64 (decide (2 ^ 64 ≤ lo1.toNat + lo2.toNat)).toNat +
      ~~~((c >>> 63) - 1#64) + BitVec.ofNat 64 (decide (2 ^ 64 ≤ s1.toNat + c.toNat)).toNat
    let T := k * M
    let T' := T + kc
    let kc' := BitVec.ofNat 64 (k.toNat * M.toNat / 2 ^ 64) + BitVec.ofNat 64 (decide (2 ^ 64 ≤ T.toNat + kc.toNat)).toNat
    let lo' := lo + T'
    let c'' := c' + BitVec.ofNat 64 (decide (2 ^ 64 ≤ lo.toNat + T'.toNat)).toNat
    (lo'.toNat : Int) + 2 ^ 64 * (c''.toInt + kc'.toNat) =
      cu.toInt * a.toNat + cv.toInt * b.toNat + c.toInt + k.toNat * M.toNat + kc.toNat ∧
      c''.toInt.natAbs ≤ 2 ^ 61 := by
  intro lo1 hi1 lo2 hi2 s1 lo c' T T' kc' lo' c''
  obtain ⟨r1, -⟩ := Divstep.rowWord cu cv a b c (by omega) (by omega)
  have cb : c'.toInt.natAbs ≤ 2 ^ 59 + 1 :=
    carry_bound lo.isLt r1 (lin_abs cu cv _ _ _ a.isLt b.isLt hb hc)
  obtain ⟨k1, kC⟩ := kWord lo k M kc
  have tc : c''.toInt = c'.toInt + (decide (2 ^ 64 ≤ lo.toNat + T'.toNat)).toNat := toInt_add_bit _ _ kC cb
  refine ⟨?_, by rw [tc]; exact natAbs_add_bit (Bool.toNat_le _) cb⟩
  rw [tc]
  have r1' : (lo.toNat : Int) + 2 ^ 64 * c'.toInt = cu.toInt * a.toNat + cv.toInt * b.toNat + c.toInt := r1
  have k1' : (lo'.toNat : Int) + 2 ^ 64 * (((decide (2 ^ 64 ≤ lo.toNat + T'.toNat)).toNat : Nat) + kc'.toNat) =
      lo.toNat + k.toNat * M.toNat + kc.toNat := k1
  push_cast at k1' ⊢
  omega

/-- `deRowValU` with the carries merged, as in the loop's word. -/
theorem deRowVal (cu cv a b c k M kc : BitVec 64) (hb : cu.toInt.natAbs + cv.toInt.natAbs ≤ 2 ^ 59)
    (hc : c.toInt.natAbs ≤ 2 ^ 61) :
    let lo1 := cu * a
    let hi1 := BitVec.ofNat 64 (cu.toNat * a.toNat / 2 ^ 64) - (a &&& (0#64 - (cu >>> 63)))
    let lo2 := cv * b
    let hi2 := BitVec.ofNat 64 (cv.toNat * b.toNat / 2 ^ 64) - (b &&& (0#64 - (cv >>> 63)))
    let s1 := lo1 + lo2
    let lo := s1 + c
    let T := k * M
    let T' := T + kc
    let kc' := BitVec.ofNat 64 (k.toNat * M.toNat / 2 ^ 64) + BitVec.ofNat 64 (decide (2 ^ 64 ≤ T.toNat + kc.toNat)).toNat
    let lo' := lo + T'
    let c'' := hi1 + hi2 + BitVec.ofNat 64 (decide (2 ^ 64 ≤ lo1.toNat + lo2.toNat)).toNat +
      ~~~((c >>> 63) - 1#64) + BitVec.ofNat 64 ((decide (2 ^ 64 ≤ s1.toNat + c.toNat)).toNat +
        (decide (2 ^ 64 ≤ lo.toNat + T'.toNat)).toNat)
    (lo'.toNat : Int) + 2 ^ 64 * (c''.toInt + kc'.toNat) =
      cu.toInt * a.toNat + cv.toInt * b.toNat + c.toInt + k.toNat * M.toNat + kc.toNat ∧
      c''.toInt.natAbs ≤ 2 ^ 61 := by
  intro lo1 hi1 lo2 hi2 s1 lo T T' kc' lo' c''
  have e : c'' = hi1 + hi2 + BitVec.ofNat 64 (decide (2 ^ 64 ≤ lo1.toNat + lo2.toNat)).toNat +
      ~~~((c >>> 63) - 1#64) + BitVec.ofNat 64 (decide (2 ^ 64 ≤ s1.toNat + c.toNat)).toNat +
      BitVec.ofNat 64 (decide (2 ^ 64 ≤ lo.toNat + T'.toNat)).toNat := by
    simp only [c'', BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [e]
  exact deRowValU cu cv a b c k M kc hb hc

/-- `deRowValU` for `prodsD` (the form `brun` leaves of the first word). -/
theorem deRowValUD (cu cv a b c k M kc : BitVec 64) (hb : cu.toInt.natAbs + cv.toInt.natAbs ≤ 2 ^ 59)
    (hc : c.toInt.natAbs ≤ 2 ^ 61) :
    let s1 := cu * a + cv * b
    let lo := s1 + c
    let T := k * M
    let T' := T + kc
    let kc' := BitVec.ofNat 64 (k.toNat * M.toNat / 2 ^ 64) + BitVec.ofNat 64 (decide (2 ^ 64 ≤ T.toNat + kc.toNat)).toNat
    let lo' := lo + T'
    let c'' := off (BitVec.ofNat 64 (cu.toNat * a.toNat / 2 ^ 64))
        (cv.toNat * b.toNat / 2 ^ 64 + (decide (2 ^ 64 ≤ (cu * a).toNat + (cv * b).toNat)).toNat) -
          (a &&& 0#64 - cu >>> 63) - (b &&& 0#64 - cv >>> 63) + ~~~(c >>> 63 - 1#64) +
        BitVec.ofNat 64 (decide (2 ^ 64 ≤ s1.toNat + c.toNat)).toNat +
        BitVec.ofNat 64 (decide (2 ^ 64 ≤ lo.toNat + T'.toNat)).toNat
    (lo'.toNat : Int) + 2 ^ 64 * (c''.toInt + kc'.toNat) =
      cu.toInt * a.toNat + cv.toInt * b.toNat + c.toInt + k.toNat * M.toNat + kc.toNat ∧
      c''.toInt.natAbs ≤ 2 ^ 61 := by
  intro s1 lo T T' kc' lo' c''
  have e : c'' = BitVec.ofNat 64 (cu.toNat * a.toNat / 2 ^ 64) - (a &&& (0#64 - (cu >>> 63))) +
      (BitVec.ofNat 64 (cv.toNat * b.toNat / 2 ^ 64) - (b &&& (0#64 - (cv >>> 63)))) +
      BitVec.ofNat 64 (decide (2 ^ 64 ≤ (cu * a).toNat + (cv * b).toNat)).toNat +
      ~~~((c >>> 63) - 1#64) + BitVec.ofNat 64 (decide (2 ^ 64 ≤ s1.toNat + c.toNat)).toNat +
      BitVec.ofNat 64 (decide (2 ^ 64 ≤ lo.toNat + T'.toNat)).toNat := by
    simp only [c'', off, ← BitVec.ofNat_add_ofNat, BitVec.sub_eq_add_neg]
    ac_rfl
  rw [e]
  exact deRowValU cu cv a b c k M kc hb hc

/-- `deRowVal` for `prodsD`, whose high words are summed before the masks are
taken off (the form `brun` leaves). -/
theorem deRowValD (cu cv a b c k M kc : BitVec 64) (hb : cu.toInt.natAbs + cv.toInt.natAbs ≤ 2 ^ 59)
    (hc : c.toInt.natAbs ≤ 2 ^ 61) :
    let s1 := cu * a + cv * b
    let lo := s1 + c
    let T := k * M
    let T' := T + kc
    let kc' := BitVec.ofNat 64 (k.toNat * M.toNat / 2 ^ 64) + BitVec.ofNat 64 (decide (2 ^ 64 ≤ T.toNat + kc.toNat)).toNat
    let lo' := lo + T'
    let c'' := off (off (BitVec.ofNat 64 (cu.toNat * a.toNat / 2 ^ 64))
        (cv.toNat * b.toNat / 2 ^ 64 + (decide (2 ^ 64 ≤ (cu * a).toNat + (cv * b).toNat)).toNat) -
          (a &&& 0#64 - cu >>> 63) - (b &&& 0#64 - cv >>> 63) + ~~~(c >>> 63 - 1#64))
        ((decide (2 ^ 64 ≤ s1.toNat + c.toNat)).toNat + (decide (2 ^ 64 ≤ lo.toNat + T'.toNat)).toNat)
    (lo'.toNat : Int) + 2 ^ 64 * (c''.toInt + kc'.toNat) =
      cu.toInt * a.toNat + cv.toInt * b.toNat + c.toInt + k.toNat * M.toNat + kc.toNat ∧
      c''.toInt.natAbs ≤ 2 ^ 61 := by
  intro s1 lo T T' kc' lo' c''
  have e : c'' = BitVec.ofNat 64 (cu.toNat * a.toNat / 2 ^ 64) - (a &&& (0#64 - (cu >>> 63))) +
      (BitVec.ofNat 64 (cv.toNat * b.toNat / 2 ^ 64) - (b &&& (0#64 - (cv >>> 63)))) +
      BitVec.ofNat 64 (decide (2 ^ 64 ≤ (cu * a).toNat + (cv * b).toNat)).toNat +
      ~~~((c >>> 63) - 1#64) + BitVec.ofNat 64 ((decide (2 ^ 64 ≤ s1.toNat + c.toNat)).toNat +
        (decide (2 ^ 64 ≤ lo.toNat + T'.toNat)).toNat) := by
    simp only [c'', off, ← BitVec.ofNat_add_ofNat, BitVec.sub_eq_add_neg]
    ac_rfl
  rw [e]
  exact deRowVal cu cv a b c k M kc hb hc

/-- A word `j + 1 < n` of the pass over `(a, b)`: words `j + 1` of `[x16]`,
`[x17]`, `[x8]` read, both rows' sums' words written to words `j` of the
first two, and on to the carries (signed in `x13`, `x25`, unsigned in
`x23`, `x30`). -/
theorem deWord_ok (s : State) {B : Addr} {Z eA eB eM : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eA) (h17 : s.gpr .x17 = off B eB) (h8 : s.gpr .x8 = off B eM)
    (hA : eA + 16 ≤ Z) (hB : eB + 16 ≤ Z) (hM : eM + 16 ≤ Z) (h28 : s.gpr .x28 = 0#64)
    (m9 : Msk s .x9 .x4) (m10 : Msk s .x10 .x5) (m19 : Msk s .x19 .x6) (m20 : Msk s .x20 .x7)
    (b1 : Cb59 s .x4 .x5) (b2 : Cb59 s .x6 .x7) (c1 : (s.gpr .x13).toInt.natAbs ≤ 2 ^ 61)
    (c2 : (s.gpr .x25).toInt.natAbs ≤ 2 ^ 61) :
    WP isa (.block deBody) s fun t => ∃ lo₁ lo₂ : BitVec 64,
      t.mem = (s.mem.writeW (off B eA) lo₁).writeW (off B eB) lo₂ ∧
      (lo₁.toNat : Int) + 2 ^ 64 * ((t.gpr .x13).toInt + (t.gpr .x23).toNat) =
        (s.gpr .x4).toInt * (word s.mem B (eA + 8)).toNat + (s.gpr .x5).toInt * (word s.mem B (eB + 8)).toNat +
        (s.gpr .x13).toInt + (s.gpr .x26).toNat * (word s.mem B (eM + 8)).toNat + (s.gpr .x23).toNat ∧
      (lo₂.toNat : Int) + 2 ^ 64 * ((t.gpr .x25).toInt + (t.gpr .x30).toNat) =
        (s.gpr .x6).toInt * (word s.mem B (eA + 8)).toNat + (s.gpr .x7).toInt * (word s.mem B (eB + 8)).toNat +
        (s.gpr .x25).toInt + (s.gpr .x27).toNat * (word s.mem B (eM + 8)).toNat + (s.gpr .x30).toNat ∧
      (t.gpr .x13).toInt.natAbs ≤ 2 ^ 61 ∧ (t.gpr .x25).toInt.natAbs ≤ 2 ^ 61 ∧
      t.gpr .x16 = off B (eA + 8) ∧ t.gpr .x17 = off B (eB + 8) ∧ t.gpr .x8 = off B (eM + 8) := by
  unfold deBody deRow prodsD carryIn kterm
  brun [h16, h17, h8, h28, hs.ld (show eA + 8 + 8 ≤ Z by omega_arith), hs.ld (show eB + 8 + 8 ≤ Z by omega_arith),
    hs.ld (show eM + 8 + 8 ≤ Z by omega_arith), hs.st (show eA + 8 ≤ Z by omega_arith),
    hs.st (show eB + 8 ≤ Z by omega_arith), exec_sbc_x, BitVec.add_zero]
  have r1 := deRowValD (s.gpr .x4) (s.gpr .x5) (word s.mem B (eA + 8)) (word s.mem B (eB + 8)) (s.gpr .x13)
    (s.gpr .x26) (word s.mem B (eM + 8)) (s.gpr .x23) b1 c1
  have r2 := deRowValD (s.gpr .x6) (s.gpr .x7) (word s.mem B (eA + 8)) (word s.mem B (eB + 8)) (s.gpr .x25)
    (s.gpr .x27) (word s.mem B (eM + 8)) (s.gpr .x30) b2 c2
  rw [m9, m10, m19, m20]
  simp only [Bool.toNat_false, BitVec.add_zero, Nat.add_zero, word] at r1 r2 ⊢
  exact ⟨_, _, rfl, r1.1, r2.1, r1.2, r2.2⟩

/-! ## The pass over `(f, g)` -/

/-- A step of a row's shifted sum: the invariant for `j + 1` words from `j`
(`Divstep.shr_step`), and the word's sum and carry. -/
theorem fgV_next {j r O o lo prev X Y x y : Nat} {c c' u v : Int}
    (hv : ((r + 2 ^ 59 * O + 2 ^ (64 * j) * 2 ^ 59 * (prev / 2 ^ 59) : Nat) : Int) +
      ((2 ^ (64 * j) * 2 ^ 64 : Nat) : Int) * c = u * X + v * Y)
    (hw : (lo : Int) + 2 ^ 64 * c' = u * x + v * y + c)
    (ho : o = prev / 2 ^ 59 + 2 ^ 5 * (lo % 2 ^ 59)) :
    ((r + 2 ^ 59 * (O + 2 ^ (64 * j) * o) + 2 ^ (64 * (j + 1)) * 2 ^ 59 * (lo / 2 ^ 59) : Nat) : Int) +
      ((2 ^ (64 * (j + 1)) * 2 ^ 64 : Nat) : Int) * c' =
        u * (X + 2 ^ (64 * j) * 2 ^ 64 * x : Nat) + v * (Y + 2 ^ (64 * j) * 2 ^ 64 * y : Nat) := by
  have st := Divstep.shr_step (W := r + 2 ^ 59 * O + 2 ^ (64 * j) * 2 ^ 59 * (prev / 2 ^ 59)) (P := 2 ^ (64 * j))
    rfl ho
  rw [show (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) by rw [Int.natCast_pow]; rfl] at hw
  rw [pow64_succ]
  generalize 2 ^ (64 * j) = P at *
  generalize 2 ^ 64 = Q at *
  generalize lo / 2 ^ 59 = L at *
  generalize 2 ^ 59 = R59 at *
  rw [← st]
  have := congrArg (fun z => (P : Int) * Q * z) hw
  push_cast at hv this ⊢
  grind

/-- Writing word `j` of two arrays apart: each one's first `j + 1` words. -/
theorem wv_write2 (m : Mem) (B : Addr) {eF eG j : Nat} (o₁ o₂ : BitVec 64) (hF : eF + 8 * j + 8 ≤ 2 ^ 64)
    (hG : eG + 8 * j + 8 ≤ 2 ^ 64) (sep : eF + 8 * (j + 1) ≤ eG ∨ eG + 8 * (j + 1) ≤ eF) :
    wv ((m.writeW (off B (eF + 8 * j)) o₁).writeW (off B (eG + 8 * j)) o₂) B eF (j + 1) =
      wv m B eF j + 2 ^ (64 * j) * o₁.toNat ∧
    wv ((m.writeW (off B (eF + 8 * j)) o₁).writeW (off B (eG + 8 * j)) o₂) B eG (j + 1) =
      wv m B eG j + 2 ^ (64 * j) * o₂.toNat := by
  constructor
  · rw [(writeW_outside _ B o₂ hG).wv (by omega_arith) (by omega_arith), wv_writeW_top _ _ _ _ _ hF]
  · rw [wv_writeW_top _ _ _ _ _ hG, (writeW_outside _ B o₁ hF).wv (by omega_arith) (by omega_arith)]

/-- Two writes, each in the next word of a range. -/
theorem Frm.write2 {m m' : Mem} {B : Addr} {eF eG j : Nat} (h : Frm B [(eF, 8 * j), (eG, 8 * j)] m m')
    (o₁ o₂ : BitVec 64) (hF : eF + 8 * j + 8 ≤ 2 ^ 64) (hG : eG + 8 * j + 8 ≤ 2 ^ 64) :
    Frm B [(eF, 8 * (j + 1)), (eG, 8 * (j + 1))] m
      ((m'.writeW (off B (eF + 8 * j)) o₁).writeW (off B (eG + 8 * j)) o₂) := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
  rw [writeW_outside _ B o₂ hG x (by omega_arith), writeW_outside _ B o₁ hF x (by omega_arith)]
  exact h x (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith)

/-- After word `j` of the pass over `(f, g)` (`[x16]`, `[x17]` at it): the
words read of each row, shifted, are its low bits `r < 2^59`, `2^59` times
the `j` words written, and the previous sum's top bits; with the carry. -/
structure FgInv (s₀ : State) (B : Addr) (Z eF eG : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x1, .x2, .x3, .x13, .x14, .x16, .x17, .x21, .x22, .x23, .x24, .x25, .x26, .x27] s₀ t
  x16 : t.gpr .x16 = off B (eF + 8 * j)
  x17 : t.gpr .x17 = off B (eG + 8 * j)
  frm : Frm B [(eF, 8 * j), (eG, 8 * j)] s₀.mem t.mem
  v₁ : ∃ r < 2 ^ 59, ((r + 2 ^ 59 * wv t.mem B eF j + 2 ^ (64 * j) * 2 ^ 59 * ((t.gpr .x26).toNat / 2 ^ 59) : Nat) : Int) +
    ((2 ^ (64 * j) * 2 ^ 64 : Nat) : Int) * (t.gpr .x13).toInt =
      (s₀.gpr .x4).toInt * wv s₀.mem B eF (j + 1) + (s₀.gpr .x5).toInt * wv s₀.mem B eG (j + 1)
  v₂ : ∃ r < 2 ^ 59, ((r + 2 ^ 59 * wv t.mem B eG j + 2 ^ (64 * j) * 2 ^ 59 * ((t.gpr .x27).toNat / 2 ^ 59) : Nat) : Int) +
    ((2 ^ (64 * j) * 2 ^ 64 : Nat) : Int) * (t.gpr .x25).toInt =
      (s₀.gpr .x6).toInt * wv s₀.mem B eF (j + 1) + (s₀.gpr .x7).toInt * wv s₀.mem B eG (j + 1)
  c₁ : (t.gpr .x13).toInt.natAbs ≤ 2 ^ 62
  c₂ : (t.gpr .x25).toInt.natAbs ≤ 2 ^ 62
  x2 : t.gpr .x2 = word s₀.mem B (eF + 8 * j)
  x3 : t.gpr .x3 = word s₀.mem B (eG + 8 * j)

theorem fgStep_ok {s₀ : State} {B : Addr} {Z n eF eG : Nat}
    (m9 : Msk s₀ .x9 .x4) (m10 : Msk s₀ .x10 .x5) (m19 : Msk s₀ .x19 .x6) (m20 : Msk s₀ .x20 .x7)
    (b1 : Cb s₀ .x4 .x5) (b2 : Cb s₀ .x6 .x7) (hF : eF + 8 * (n + 1) ≤ Z) (hG : eG + 8 * (n + 1) ≤ Z)
    (sep : eF + 8 * (n + 1) ≤ eG ∨ eG + 8 * (n + 1) ≤ eF)
    {j : Nat} (hj : j < n) {t : State} (hI : FgInv s₀ B Z eF eG j t) :
    WP isa (.block (fgBody ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      FgInv s₀ B Z eF eG (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have k : ∀ r : Reg, r ∉ [.x1, .x2, .x3, .x13, .x14, .x16, .x17, .x21, .x22, .x23, .x24, .x25, .x26, .x27] →
      t.gpr r = s₀.gpr r := fun r hr => hI.keep.gpr r hr
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x1, .x2, .x3, .x13, .x16, .x17, .x21, .x22, .x23, .x24, .x25, .x26, .x27]
    (fgWord_ok t hI.scr hI.x16 hI.x17 (by omega_arith) (by omega_arith)
      (by unfold Msk; rw [k _ (by decide), k _ (by decide), m9]) (by unfold Msk; rw [k _ (by decide), k _ (by decide), m10])
      (by unfold Msk; rw [k _ (by decide), k _ (by decide), m19]) (by unfold Msk; rw [k _ (by decide), k _ (by decide), m20])
      (by unfold Cb; rw [k _ (by decide), k _ (by decide)]; exact b1) (by unfold Cb; rw [k _ (by decide), k _ (by decide)]; exact b2)
      hI.c₁ hI.c₂)
    (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨o₁, o₂, hm, w₁, w₂, cb₁, cb₂, ho₁, ho₂, h16, h17, h2, h3⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', _⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have hmem : t'.mem = (t.mem.writeW (off B (eF + 8 * j)) o₁).writeW (off B (eG + 8 * j)) o₂ := hm'.trans hm
  -- The words read are the first ones'.
  have rf : word t.mem B (eF + 8 * j + 8) = word s₀.mem B (eF + 8 * j + 8) :=
    hI.frm.word_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith)
      (by omega_arith)
  have rg : word t.mem B (eG + 8 * j + 8) = word s₀.mem B (eG + 8 * j + 8) :=
    hI.frm.word_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith)
      (by omega_arith)
  obtain ⟨wf, wg⟩ := wv_write2 t.mem B o₁ o₂ (eF := eF) (eG := eG) (j := j) (by omega_arith) (by omega_arith) (by omega_arith)
  have e13 : t'.gpr .x13 = t₁.gpr .x13 := k'.gpr .x13 (by decide)
  have e25 : t'.gpr .x25 = t₁.gpr .x25 := k'.gpr .x25 (by decide)
  have e26 : t'.gpr .x26 = t₁.gpr .x26 := k'.gpr .x26 (by decide)
  have e27 : t'.gpr .x27 = t₁.gpr .x27 := k'.gpr .x27 (by decide)
  have eX : wv s₀.mem B eF (j + 1 + 1) = wv s₀.mem B eF (j + 1) +
      2 ^ (64 * j) * 2 ^ 64 * (word s₀.mem B (eF + 8 * j + 8)).toNat := by
    rw [wv, pow64_succ, show eF + 8 * (j + 1) = eF + 8 * j + 8 by omega_arith]
  have eY : wv s₀.mem B eG (j + 1 + 1) = wv s₀.mem B eG (j + 1) +
      2 ^ (64 * j) * 2 ^ 64 * (word s₀.mem B (eG + 8 * j + 8)).toNat := by
    rw [wv, pow64_succ, show eG + 8 * (j + 1) = eG + 8 * j + 8 by omega_arith]
  have kc : ∀ r : Reg, r ∉ [.x1, .x2, .x3, .x13, .x14, .x16, .x17, .x21, .x22, .x23, .x24, .x25, .x26, .x27] →
      t.gpr r = s₀.gpr r := k
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc],
    by rw [hmem]; exact Frm.write2 hI.frm o₁ o₂ (by omega_arith) (by omega_arith), ?_, ?_,
    by rw [e13]; exact cb₁, by rw [e25]; exact cb₂,
    by rw [k'.gpr .x2 (by decide), h2, rf, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x3 (by decide), h3, rg, Nat.mul_succ, Nat.add_assoc]⟩
  · obtain ⟨r, hr, hv⟩ := hI.v₁
    refine ⟨r, hr, ?_⟩
    rw [hmem, wf, e13, e26]
    rw [rf, rg, k .x4 (by decide), k .x5 (by decide)] at w₁
    rw [eX, eY]
    exact fgV_next hv w₁ ho₁
  · obtain ⟨r, hr, hv⟩ := hI.v₂
    refine ⟨r, hr, ?_⟩
    rw [hmem, wg, e25, e27]
    rw [rf, rg, k .x6 (by decide), k .x7 (by decide)] at w₂
    rw [eX, eY]
    exact fgV_next hv w₂ ho₂

/-- Word 0 of the pass over `(f, g)`, from zero carries, and `x14 := n`. -/
theorem fgHead_ok (s : State) {B : Addr} {Z eF eG n : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eF) (h17 : s.gpr .x17 = off B eG) (hF : eF + 8 ≤ Z) (hG : eG + 8 ≤ Z)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (m9 : Msk s .x9 .x4) (m10 : Msk s .x10 .x5) (m19 : Msk s .x19 .x6) (m20 : Msk s .x20 .x7)
    (b1 : Cb s .x4 .x5) (b2 : Cb s .x6 .x7) :
    WP isa (.block (([ld .x2 .x16, ld .x3 .x17, movi .x13 0, movi .x25 0] : List Instr) ++
      fgRow .x4 .x5 .x9 .x10 .x13 .x26 ++ fgRow .x6 .x7 .x19 .x20 .x25 .x27 ++ ([mov .x14 .x12] : List Instr))) s
      fun t => (((t.gpr .x26).toNat : Int) + 2 ^ 64 * (t.gpr .x13).toInt =
          (s.gpr .x4).toInt * (word s.mem B eF).toNat + (s.gpr .x5).toInt * (word s.mem B eG).toNat ∧
        ((t.gpr .x27).toNat : Int) + 2 ^ 64 * (t.gpr .x25).toInt =
          (s.gpr .x6).toInt * (word s.mem B eF).toNat + (s.gpr .x7).toInt * (word s.mem B eG).toNat ∧
        (t.gpr .x13).toInt.natAbs ≤ 2 ^ 62 ∧ (t.gpr .x25).toInt.natAbs ≤ 2 ^ 62 ∧
        t.gpr .x14 = BitVec.ofNat 64 n ∧ t.gpr .x2 = word s.mem B eF ∧ t.gpr .x3 = word s.mem B eG ∧
        t.mem = s.mem) ∧
      Keep [.x2, .x3, .x13, .x14, .x21, .x22, .x23, .x25, .x26, .x27] s t := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  unfold fgRow prods carryIn
  brun [h16, h17, h12, hs.ld hF, hs.ld hG, exec_sbc_x]
  have r1 := Divstep.rowWord (s.gpr .x4) (s.gpr .x5) (word s.mem B eF) (word s.mem B eG) (BitVec.setWidth 64 0#16)
    b1 (by decide)
  have r2 := Divstep.rowWord (s.gpr .x6) (s.gpr .x7) (word s.mem B eF) (word s.mem B eG) (BitVec.setWidth 64 0#16)
    b2 (by decide)
  have z : (BitVec.setWidth 64 0#16).toInt = 0 := by decide
  rw [m9, m10, m19, m20]
  simp only [Bool.toNat_false, BitVec.add_zero, Nat.add_zero, word, z, Int.add_zero] at r1 r2 ⊢
  exact ⟨r1.1, r2.1, r1.2, r2.2⟩

theorem eq_zero_of_mul_lt {r R K : Int} (h : r = R * K) (h0 : 0 ≤ r) (hR : r < R) : K = 0 := by
  rcases Int.lt_trichotomy K 0 with hk | hk | hk
  · have : R * K < 0 := Int.mul_neg_of_pos_of_neg (by omega) hk
    omega
  · exact hk
  · have : R ≤ R * K := by
      have := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ K by omega) (show 0 ≤ R by omega)
      rwa [Int.mul_one] at this
    omega

/-- The end of a row over `(f, g)`: with the carry corrected for the inputs'
signs and word `n` written, the words written are `f'` modulo `2^(64 (n + 1))`. -/
theorem fgFinal {n r O prev X Y : Nat} {c u v f' : Int} {c' : BitVec 64} {xs ys : Prop} [Decidable xs] [Decidable ys]
    (hr : r < 2 ^ 59)
    (hv : ((r + 2 ^ 59 * O + 2 ^ (64 * n) * 2 ^ 59 * (prev / 2 ^ 59) : Nat) : Int) +
      ((2 ^ (64 * n) * 2 ^ 64 : Nat) : Int) * c = u * X + v * Y)
    (hc' : c'.toInt = c - (if xs then 0 else u) - (if ys then 0 else v))
    (hsX : Divstep.sgn (n + 1) X = X - (if xs then 0 else ((2 ^ (64 * n) * 2 ^ 64 : Nat) : Int)))
    (hsY : Divstep.sgn (n + 1) Y = Y - (if ys then 0 else ((2 ^ (64 * n) * 2 ^ 64 : Nat) : Int)))
    (ef : u * Divstep.sgn (n + 1) X + v * Divstep.sgn (n + 1) Y = 2 ^ 59 * f') :
    ∃ e : Int, ((O + 2 ^ (64 * n) * (prev / 2 ^ 59 + 2 ^ 5 * (c'.toNat % 2 ^ 59)) : Nat) : Int) +
      ((2 ^ (64 * n) * 2 ^ 64 : Nat) : Int) * e = f' := by
  have st := Divstep.shr_step (W := r + 2 ^ 59 * O + 2 ^ (64 * n) * 2 ^ 59 * (prev / 2 ^ 59)) (P := 2 ^ (64 * n))
    (s0 := prev) (s1 := c'.toNat) rfl rfl
  -- `c'` as a natural number and its sign.
  obtain ⟨b, hb, tn⟩ : ∃ b : Int, (b = 0 ∨ b = 1) ∧ (c'.toNat : Int) = c'.toInt + 2 ^ 64 * b := by
    rw [BitVec.toInt_eq_toNat_cond]
    split
    · exact ⟨0, .inl rfl, by omega⟩
    · exact ⟨1, .inr rfl, by omega⟩
  rw [show (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) by rw [Int.natCast_pow]; rfl] at tn
  rw [show (2 : Int) ^ 59 = ((2 ^ 59 : Nat) : Int) by rw [Int.natCast_pow]; rfl] at ef
  rw [hsX, hsY] at ef
  generalize c'.toNat / 2 ^ 59 = m at st
  generalize hP : 2 ^ (64 * n) = P at *
  generalize hQ : 2 ^ 64 = Q at *
  have hQR : Q = 2 ^ 59 * 2 ^ 5 := by rw [← hQ, ← Nat.pow_add]
  generalize 2 ^ 5 = F at *
  generalize hR : 2 ^ 59 = R at *
  generalize hX' : O + P * (prev / R + F * (c'.toNat % R)) = X' at st ⊢
  refine ⟨m - F * b, ?_⟩
  -- `2^59 f' = r + 2^59 (X' + P Q (m - F b))`.
  have hS : (R : Int) * f' = r + R * (X' + P * Q * (m - F * b)) := by
    have e1 : ((_ : Nat) : Int) = _ := congrArg (fun z : Nat => (z : Int)) st
    subst hQR
    push_cast at e1 hv tn ef ⊢
    rw [← ef]
    by_cases hx : xs <;> by_cases hy : ys <;> simp only [hx, hy, ite_true, ite_false] at hc' ef <;> grind
  have hR0 : (0 : Int) < R := by rw [← hR]; exact Int.natCast_pos.mpr (Nat.two_pow_pos 59)
  have hK := eq_zero_of_mul_lt (r := r) (R := R) (K := f' - (X' + P * Q * (m - F * b)))
    (by rw [Int.mul_sub, hS, Int.add_sub_cancel]) (by omega) (by exact_mod_cast hr)
  rw [Int.sub_eq_zero.mp hK]
  push_cast
  rfl

theorem toInt_sub_small (x y : BitVec 64) (h : (x.toInt - y.toInt).natAbs < 2 ^ 63) :
    (x - y).toInt = x.toInt - y.toInt := by
  rw [BitVec.toInt_sub]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- The carry less the coefficients where the top words are negative. -/
theorem topFixVal (c a b u v : BitVec 64) (hc : c.toInt.natAbs ≤ 2 ^ 62)
    (huv : u.toInt.natAbs + v.toInt.natAbs ≤ 2 ^ 59) :
    (c - ((0#64 - (a >>> 63)) &&& u) - ((0#64 - (b >>> 63)) &&& v)).toInt =
      c.toInt - (if a.toNat < 2 ^ 63 then 0 else u.toInt) - (if b.toNat < 2 ^ 63 then 0 else v.toInt) := by
  rw [Divstep.signMask_eq, Divstep.signMask_eq]
  by_cases ha : a.toNat < 2 ^ 63 <;> by_cases hb : b.toNat < 2 ^ 63 <;>
    simp only [ha, hb, ite_true, ite_false, BitVec.zero_and, BitVec.allOnes_and, BitVec.sub_zero, Int.sub_zero]
  · exact toInt_sub_small _ _ (by omega)
  · exact toInt_sub_small _ _ (by omega)
  · rw [toInt_sub_small _ _ (by rw [toInt_sub_small _ _ (by omega)]; omega), toInt_sub_small _ _ (by omega)]

/-- The end of the pass over `(f, g)`: the carries corrected for the top
words' signs (`x2`, `x3`), and words `n` written. -/
theorem fgTail_ok (s : State) {B : Addr} {Z eF eG : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eF) (h17 : s.gpr .x17 = off B eG) (hF : eF + 8 ≤ Z) (hG : eG + 8 ≤ Z)
    (b1 : Cb59 s .x4 .x5) (b2 : Cb59 s .x6 .x7) (c1 : (s.gpr .x13).toInt.natAbs ≤ 2 ^ 62)
    (c2 : (s.gpr .x25).toInt.natAbs ≤ 2 ^ 62) :
    WP isa (.block (topFix .x13 .x4 .x5 ++ topFix .x25 .x6 .x7 ++
      ([.extr .x .x22 .x13 .x26 59, st .x22 .x16, .extr .x .x22 .x25 .x27 59, st .x22 .x17] : List Instr))) s
      fun t => ∃ o₁ o₂ c₁ c₂ : BitVec 64, t.mem = (s.mem.writeW (off B eF) o₁).writeW (off B eG) o₂ ∧
        c₁.toInt = (s.gpr .x13).toInt - (if (s.gpr .x2).toNat < 2 ^ 63 then 0 else (s.gpr .x4).toInt) -
          (if (s.gpr .x3).toNat < 2 ^ 63 then 0 else (s.gpr .x5).toInt) ∧
        c₂.toInt = (s.gpr .x25).toInt - (if (s.gpr .x2).toNat < 2 ^ 63 then 0 else (s.gpr .x6).toInt) -
          (if (s.gpr .x3).toNat < 2 ^ 63 then 0 else (s.gpr .x7).toInt) ∧
        o₁.toNat = (s.gpr .x26).toNat / 2 ^ 59 + 2 ^ 5 * (c₁.toNat % 2 ^ 59) ∧
        o₂.toNat = (s.gpr .x27).toNat / 2 ^ 59 + 2 ^ 5 * (c₂.toNat % 2 ^ 59) := by
  unfold topFix
  brun [h16, h17, hs.st hF, hs.st hG, exec_extr_x, show BitVec.setWidth 64 0#16 = 0#64 from rfl]
  exact ⟨_, _, _, _, rfl, topFixVal _ _ _ _ _ (by omega) b1, topFixVal _ _ _ _ _ (by omega) b2,
    Divstep.extr59 _ _, Divstep.extr59 _ _⟩

/-- The value of a signed number of `n + 1` words from its top word's sign. -/
theorem sgn_top {n W x : Nat} (hW : W < 2 ^ (64 * n)) (hx : x < 2 ^ 64) :
    Divstep.sgn (n + 1) (W + 2 ^ (64 * n) * x) =
      (W + 2 ^ (64 * n) * x : Nat) - (if x < 2 ^ 63 then 0 else ((2 ^ (64 * n) * 2 ^ 64 : Nat) : Int)) := by
  unfold Divstep.sgn
  have e := Divstep.top_sign hW hx
  by_cases h : x < 2 ^ 63
  · rw [ite_eq_left (e.mpr h), ite_eq_left h, Int.sub_zero]
  · rw [ite_eq_right (fun h' => h (e.mp h')), ite_eq_right h, ← pow64_succ]
    push_cast; rfl

/-- The invariant before the loop, from word 0. -/
theorem fgInit_val {lo : Nat} {c u v : Int} {x y : Nat} (hw : (lo : Int) + 2 ^ 64 * c = u * x + v * y) :
    ((lo % 2 ^ 59 + 2 ^ 59 * 0 + 2 ^ (64 * 0) * 2 ^ 59 * (lo / 2 ^ 59) : Nat) : Int) +
      ((2 ^ (64 * 0) * 2 ^ 64 : Nat) : Int) * c = u * (0 + 2 ^ (64 * 0) * x : Nat) + v * (0 + 2 ^ (64 * 0) * y : Nat) := by
  have := Nat.mod_add_div lo (2 ^ 59)
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero]
  rw [show (lo % 2 ^ 59 + 2 ^ 59 * (lo / 2 ^ 59)) = lo by omega]
  rw [show ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 by rw [Int.natCast_pow]; rfl]
  exact hw

/-- `fgPass f g`: `(f, g) := (u f + v g, q f + r g) / 2^59` modulo `2^(64 (n + 1))`,
the matrix in `x4`–`x7` with its sign masks, for `u f + v g` and `q f + r g`
multiples of `2^59` as signed numbers of `n + 1` words. -/
theorem fgPass_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hn1 : 1 ≤ n) (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iF iG : Nat}
    (hF : iF < 16) (hG : iG < 16) (dFG : iF ≠ iG)
    (m9 : Msk s .x9 .x4) (m10 : Msk s .x10 .x5) (m19 : Msk s .x19 .x6) (m20 : Msk s .x20 .x7)
    (b1 : Cb59 s .x4 .x5) (b2 : Cb59 s .x6 .x7) {f' g' : Int}
    (ef : (s.gpr .x4).toInt * Divstep.sgn (n + 1) (wv s.mem B (slot w iF) (n + 1)) +
      (s.gpr .x5).toInt * Divstep.sgn (n + 1) (wv s.mem B (slot w iG) (n + 1)) = 2 ^ 59 * f')
    (eg : (s.gpr .x6).toInt * Divstep.sgn (n + 1) (wv s.mem B (slot w iF) (n + 1)) +
      (s.gpr .x7).toInt * Divstep.sgn (n + 1) (wv s.mem B (slot w iG) (n + 1)) = 2 ^ 59 * g') :
    WP isa (fgPass iF iG) s fun t =>
      (∃ e : Int, (wv t.mem B (slot w iF) (n + 1) : Int) + ((2 ^ (64 * (n + 1)) : Nat) : Int) * e = f') ∧
      (∃ e : Int, (wv t.mem B (slot w iG) (n + 1) : Int) + ((2 ^ (64 * (n + 1)) : Nat) : Int) * e = g') ∧
      Frm B [(slot w iF, 8 * (n + 1)), (slot w iG, 8 * (n + 1))] s.mem t.mem ∧
      Keep [.x1, .x2, .x3, .x13, .x14, .x16, .x17, .x21, .x22, .x23, .x24, .x25, .x26, .x27] s t := by
  have hn' := hs.nowrap
  have sF := Nat.le_trans (slot_lt (w := w) hF) hZ
  have sG := Nat.le_trans (slot_lt (w := w) hG) hZ
  have sep : slot w iF + 8 * (n + 1) ≤ slot w iG ∨ slot w iG + 8 * (n + 1) ≤ slot w iF := by
    rcases slot_sep (w := w) dFG with h | h <;> [exact .inl (by omega_arith); exact .inr (by omega_arith)]
  have cb1 : Cb s .x4 .x5 := by unfold Cb; unfold Cb59 at b1; omega
  have cb2 : Cb s .x6 .x7 := by unfold Cb; unfold Cb59 at b2; omega
  unfold fgPass
  rw [show base iF .x16 ++ base iG .x17 ++ ([ld .x2 .x16, ld .x3 .x17, movi .x13 0, movi .x25 0] : List Instr) ++
      fgRow .x4 .x5 .x9 .x10 .x13 .x26 ++ fgRow .x6 .x7 .x19 .x20 .x25 .x27 ++ ([mov .x14 .x12] : List Instr) =
      (base iF .x16 ++ base iG .x17) ++ (([ld .x2 .x16, ld .x3 .x17, movi .x13 0, movi .x25 0] : List Instr) ++
      fgRow .x4 .x5 .x9 .x10 .x13 .x26 ++ fgRow .x6 .x7 .x19 .x20 .x25 .x27 ++ ([mov .x14 .x12] : List Instr)) by simp]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (base2_ok iF iG .x16 .x17 h0 h11)
    fun s₁ ⟨⟨h16, h17, m₁, _⟩, k₁⟩ => ?_))
  have g₁ : ∀ r : Reg, r ≠ .x16 → r ≠ .x17 → s₁.gpr r = s.gpr r := fun r a b => k₁.gpr r (by simp [a, b])
  refine WP.mono (fgHead_ok s₁ (hs.congr k₁.wr) h16 h17 (by omega_arith) (by omega_arith)
      ((g₁ _ (by decide) (by decide)).trans h12)
      (by unfold Msk; rw [g₁ _ (by decide) (by decide), g₁ _ (by decide) (by decide), m9])
      (by unfold Msk; rw [g₁ _ (by decide) (by decide), g₁ _ (by decide) (by decide), m10])
      (by unfold Msk; rw [g₁ _ (by decide) (by decide), g₁ _ (by decide) (by decide), m19])
      (by unfold Msk; rw [g₁ _ (by decide) (by decide), g₁ _ (by decide) (by decide), m20])
      (by unfold Cb; rw [g₁ _ (by decide) (by decide), g₁ _ (by decide) (by decide)]; exact cb1)
      (by unfold Cb; rw [g₁ _ (by decide) (by decide), g₁ _ (by decide) (by decide)]; exact cb2))
    fun s₂ ⟨⟨w₁, w₂, c₁, c₂, h14, h2, h3, m₂⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hm₂ : s₂.mem = s.mem := m₂.trans m₁
  -- The loop over words `1` to `n`.
  have I0 : FgInv s₂ B Z (slot w iF) (slot w iG) 0 s₂ := by
    refine ⟨hs.congr k12.wr, Keep.refl _ _, by rw [(k₂.gpr .x16 (by decide)).trans h16]; rfl,
      by rw [(k₂.gpr .x17 (by decide)).trans h17]; rfl, Frm.refl _ _ _, ⟨(s₂.gpr .x26).toNat % 2 ^ 59, Nat.mod_lt _ (by decide), ?_⟩,
      ⟨(s₂.gpr .x27).toNat % 2 ^ 59, Nat.mod_lt _ (by decide), ?_⟩, c₁, c₂, by rw [h2, m₂]; rfl, by rw [h3, m₂]; rfl⟩
    · simp only [wv]
      rw [m₂, k₂.gpr .x4 (by decide), k₂.gpr .x5 (by decide)]
      exact fgInit_val w₁
    · simp only [wv]
      rw [m₂, k₂.gpr .x6 (by decide), k₂.gpr .x7 (by decide)]
      exact fgInit_val w₂
  have r4 := k12.gpr .x4 (by decide); have r5 := k12.gpr .x5 (by decide)
  have r6 := k12.gpr .x6 (by decide); have r7 := k12.gpr .x7 (by decide)
  refine WP.seq (WP.mono (wp_countdown (N := n) (by omega_arith) (by omega_arith)
    (FgInv s₂ B Z (slot w iF) (slot w iG))
    (fun j hj t hI _ => fgStep_ok
      (by unfold Msk; rw [k12.gpr .x9 (by decide), r4, m9]) (by unfold Msk; rw [k12.gpr .x10 (by decide), r5, m10])
      (by unfold Msk; rw [k12.gpr .x19 (by decide), r6, m19]) (by unfold Msk; rw [k12.gpr .x20 (by decide), r7, m20])
      (by unfold Cb; rw [r4, r5]; exact cb1) (by unfold Cb; rw [r6, r7]; exact cb2)
      (by omega_arith) (by omega_arith) sep hj hI) I0 h14) fun u hI => ?_)
  have ku : ∀ r : Reg, r ∉ [.x1, .x2, .x3, .x13, .x14, .x16, .x17, .x21, .x22, .x23, .x24, .x25, .x26, .x27] →
      u.gpr r = s₂.gpr r := fun r hr => hI.keep.gpr r hr
  refine WP.mono (WP.keep [.x13, .x21, .x22, .x23, .x25] (fgTail_ok u hI.scr hI.x16 hI.x17 (by omega_arith)
    (by omega_arith) (by unfold Cb59; rw [ku .x4 (by decide), ku .x5 (by decide), r4, r5]; exact b1)
    (by unfold Cb59; rw [ku .x6 (by decide), ku .x7 (by decide), r6, r7]; exact b2) hI.c₁ hI.c₂)
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨o₁, o₂, c₁', c₂', hmt, hc1, hc2, ho1, ho2⟩, kt⟩ => ?_
  obtain ⟨wf, wg⟩ := wv_write2 u.mem B o₁ o₂ (eF := slot w iF) (eG := slot w iG) (j := n) (by omega_arith)
    (by omega_arith) (by omega_arith)
  -- The inputs as signed numbers, from their top words.
  have tX : wv s₂.mem B (slot w iF) (n + 1) =
      wv s₂.mem B (slot w iF) n + 2 ^ (64 * n) * (u.gpr .x2).toNat := by rw [hI.x2, wv]
  have tY : wv s₂.mem B (slot w iG) (n + 1) =
      wv s₂.mem B (slot w iG) n + 2 ^ (64 * n) * (u.gpr .x3).toNat := by rw [hI.x3, wv]
  have sX := sgn_top (wv_lt s₂.mem B (slot w iF) n) (u.gpr .x2).isLt
  have sY := sgn_top (wv_lt s₂.mem B (slot w iG) n) (u.gpr .x3).isLt
  rw [← tX] at sX; rw [← tY] at sY
  have p1 : ((2 ^ (64 * (n + 1)) : Nat) : Int) = ((2 ^ (64 * n) * 2 ^ 64 : Nat) : Int) := by rw [pow64_succ]
  refine ⟨?_, ?_, ?_, ((k12.trans hI.keep).trans kt).mono (by decide)⟩
  · obtain ⟨r, hr, hv⟩ := hI.v₁
    rw [hmt, wf, ho1, p1]
    rw [ku .x4 (by decide), ku .x5 (by decide)] at hc1
    exact fgFinal hr hv hc1 sX sY (by rw [r4, r5, hm₂]; exact ef)
  · obtain ⟨r, hr, hv⟩ := hI.v₂
    rw [hmt, wg, ho2, p1]
    rw [ku .x6 (by decide), ku .x7 (by decide)] at hc2
    have := fgFinal (X := wv s₂.mem B (slot w iF) (n + 1)) (Y := wv s₂.mem B (slot w iG) (n + 1)) hr hv hc2 sX sY
      (by rw [r6, r7, hm₂]; exact eg)
    exact this
  · rw [← hm₂, hmt]; exact Frm.write2 hI.frm o₁ o₂ (by omega_arith) (by omega_arith)

/-! ## The pass over `(a, b)` -/

/-- A step of a row's sum over `(a, b)`: the low word `s0` (dropped), the
words written, and the carries, for `j + 1` words from `j`. -/
theorem deV_next {j s0 O lo X Y M x y mw k : Nat} {c c' kc kc' u v : Int}
    (hv : ((s0 + 2 ^ 64 * O : Nat) : Int) + ((2 ^ (64 * j) * 2 ^ 64 : Nat) : Int) * (c + kc) =
      u * X + v * Y + k * M)
    (hw : (lo : Int) + 2 ^ 64 * (c' + kc') = u * x + v * y + c + k * mw + kc) :
    ((s0 + 2 ^ 64 * (O + 2 ^ (64 * j) * lo) : Nat) : Int) + ((2 ^ (64 * (j + 1)) * 2 ^ 64 : Nat) : Int) * (c' + kc') =
      u * (X + 2 ^ (64 * j) * 2 ^ 64 * x : Nat) + v * (Y + 2 ^ (64 * j) * 2 ^ 64 * y : Nat) +
        k * (M + 2 ^ (64 * j) * 2 ^ 64 * mw : Nat) := by
  rw [show (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) by rw [Int.natCast_pow]; rfl] at hw
  rw [pow64_succ]
  generalize 2 ^ (64 * j) = P at *
  generalize 2 ^ 64 = Q at *
  have := congrArg (fun z => (P : Int) * Q * z) hw
  push_cast at hv this ⊢
  grind

/-- After word `j` of the pass over `(a, b)` (`[x16]`, `[x17]`, `[x8]` at it):
each row's words read are its low word `s0`, `2^64` times the `j` words
written and `2^(64 (j + 1))` times its carries. -/
structure DeInv (s₀ : State) (B : Addr) (Z eA eB eM : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x1, .x2, .x3, .x8, .x13, .x14, .x16, .x17, .x21, .x22, .x23, .x24, .x25, .x30] s₀ t
  x16 : t.gpr .x16 = off B (eA + 8 * j)
  x17 : t.gpr .x17 = off B (eB + 8 * j)
  x8 : t.gpr .x8 = off B (eM + 8 * j)
  frm : Frm B [(eA, 8 * j), (eB, 8 * j)] s₀.mem t.mem
  v₁ : ∃ s0 < 2 ^ 64, ((s0 + 2 ^ 64 * wv t.mem B eA j : Nat) : Int) +
    ((2 ^ (64 * j) * 2 ^ 64 : Nat) : Int) * ((t.gpr .x13).toInt + (t.gpr .x23).toNat) =
      (s₀.gpr .x4).toInt * wv s₀.mem B eA (j + 1) + (s₀.gpr .x5).toInt * wv s₀.mem B eB (j + 1) +
        (s₀.gpr .x26).toNat * wv s₀.mem B eM (j + 1)
  v₂ : ∃ s0 < 2 ^ 64, ((s0 + 2 ^ 64 * wv t.mem B eB j : Nat) : Int) +
    ((2 ^ (64 * j) * 2 ^ 64 : Nat) : Int) * ((t.gpr .x25).toInt + (t.gpr .x30).toNat) =
      (s₀.gpr .x6).toInt * wv s₀.mem B eA (j + 1) + (s₀.gpr .x7).toInt * wv s₀.mem B eB (j + 1) +
        (s₀.gpr .x27).toNat * wv s₀.mem B eM (j + 1)
  c₁ : (t.gpr .x13).toInt.natAbs ≤ 2 ^ 61
  c₂ : (t.gpr .x25).toInt.natAbs ≤ 2 ^ 61

theorem deStep_ok {s₀ : State} {B : Addr} {Z n eA eB eM : Nat} (h28 : s₀.gpr .x28 = 0#64)
    (m9 : Msk s₀ .x9 .x4) (m10 : Msk s₀ .x10 .x5) (m19 : Msk s₀ .x19 .x6) (m20 : Msk s₀ .x20 .x7)
    (b1 : Cb59 s₀ .x4 .x5) (b2 : Cb59 s₀ .x6 .x7) (hA : eA + 8 * (n + 1) ≤ Z) (hB : eB + 8 * (n + 1) ≤ Z)
    (hM : eM + 8 * (n + 1) ≤ Z) (sep : eA + 8 * (n + 1) ≤ eB ∨ eB + 8 * (n + 1) ≤ eA)
    (sAM : eA + 8 * (n + 1) ≤ eM ∨ eM + 8 * (n + 1) ≤ eA) (sBM : eB + 8 * (n + 1) ≤ eM ∨ eM + 8 * (n + 1) ≤ eB)
    {j : Nat} (hj : j + 1 < n) {t : State} (hI : DeInv s₀ B Z eA eB eM j t) :
    WP isa (.block (deBody ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      DeInv s₀ B Z eA eB eM (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have k : ∀ r : Reg, r ∉ [.x1, .x2, .x3, .x8, .x13, .x14, .x16, .x17, .x21, .x22, .x23, .x24, .x25, .x30] →
      t.gpr r = s₀.gpr r := fun r hr => hI.keep.gpr r hr
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x1, .x2, .x3, .x8, .x13, .x16, .x17, .x21, .x22, .x23, .x24, .x25, .x30]
    (deWord_ok t hI.scr hI.x16 hI.x17 hI.x8 (by omega_arith) (by omega_arith) (by omega_arith)
      (by rw [k _ (by decide), h28])
      (by unfold Msk; rw [k _ (by decide), k _ (by decide), m9]) (by unfold Msk; rw [k _ (by decide), k _ (by decide), m10])
      (by unfold Msk; rw [k _ (by decide), k _ (by decide), m19]) (by unfold Msk; rw [k _ (by decide), k _ (by decide), m20])
      (by unfold Cb59; rw [k _ (by decide), k _ (by decide)]; exact b1)
      (by unfold Cb59; rw [k _ (by decide), k _ (by decide)]; exact b2) hI.c₁ hI.c₂)
    (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨lo₁, lo₂, hm, w₁, w₂, cb₁, cb₂, h16, h17, h8⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', _⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have hmem : t'.mem = (t.mem.writeW (off B (eA + 8 * j)) lo₁).writeW (off B (eB + 8 * j)) lo₂ := hm'.trans hm
  have frw : ∀ {e : Nat}, e + 8 ≤ Z → (e + 8 ≤ eA ∨ eA + 8 * j ≤ e) → (e + 8 ≤ eB ∨ eB + 8 * j ≤ e) →
      word t.mem B e = word s₀.mem B e := fun {e} h a b =>
    hI.frm.word_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith)
      (by omega_arith)
  have ra := frw (e := eA + 8 * j + 8) (by omega_arith) (by omega_arith) (by omega_arith)
  have rb := frw (e := eB + 8 * j + 8) (by omega_arith) (by omega_arith) (by omega_arith)
  have rm := frw (e := eM + 8 * j + 8) (by omega_arith) (by omega_arith) (by omega_arith)
  obtain ⟨wa, wb⟩ := wv_write2 t.mem B lo₁ lo₂ (eF := eA) (eG := eB) (j := j) (by omega_arith) (by omega_arith)
    (by omega_arith)
  have eX : ∀ e, wv s₀.mem B e (j + 1 + 1) = wv s₀.mem B e (j + 1) +
      2 ^ (64 * j) * 2 ^ 64 * (word s₀.mem B (e + 8 * j + 8)).toNat := fun e => by
    rw [wv, pow64_succ, show e + 8 * (j + 1) = e + 8 * j + 8 by omega_arith]
  have e23 : t'.gpr .x23 = t₁.gpr .x23 := k'.gpr .x23 (by decide)
  have e30 : t'.gpr .x30 = t₁.gpr .x30 := k'.gpr .x30 (by decide)
  have e13 : t'.gpr .x13 = t₁.gpr .x13 := k'.gpr .x13 (by decide)
  have e25 : t'.gpr .x25 = t₁.gpr .x25 := k'.gpr .x25 (by decide)
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x8 (by decide), h8, Nat.mul_succ, Nat.add_assoc],
    by rw [hmem]; exact Frm.write2 hI.frm lo₁ lo₂ (by omega_arith) (by omega_arith), ?_, ?_,
    by rw [e13]; exact cb₁, by rw [e25]; exact cb₂⟩
  · obtain ⟨s0, hs0, hv⟩ := hI.v₁
    refine ⟨s0, hs0, ?_⟩
    rw [hmem, wa, e13, e23, eX, eX, eX]
    rw [ra, rb, rm, k .x4 (by decide), k .x5 (by decide), k .x26 (by decide)] at w₁
    exact deV_next hv w₁
  · obtain ⟨s0, hs0, hv⟩ := hI.v₂
    refine ⟨s0, hs0, ?_⟩
    rw [hmem, wb, e25, e30, eX, eX, eX]
    rw [ra, rb, rm, k .x6 (by decide), k .x7 (by decide), k .x27 (by decide)] at w₂
    exact deV_next hv w₂

/-- The code of word 0 of the pass over `(a, b)`. -/
def deHead : List Instr :=
  ([ld .x2 .x16, ld .x3 .x17, .mul .x .x22 .x4 .x2, .madd .x .x22 .x5 .x3 .x22, .mul .x .x26 .x22 .x28,
    .mul .x .x22 .x6 .x2, .madd .x .x22 .x7 .x3 .x22, .mul .x .x27 .x22 .x28,
    movi .x28 0, movi .x23 0, movi .x30 0, movi .x13 0, movi .x25 0] : List Instr) ++
  deRow .x4 .x5 .x9 .x10 .x26 .x23 .x13 .x1 0 ++ deRow .x6 .x7 .x19 .x20 .x27 .x30 .x25 .x24 0

/-- Word 0 of the pass over `(a, b)`: the multiples `kᵢ` of `m` from the
rows' low words and `-m⁻¹` (`x28`, then the zero register), and the rows' first sums. -/
theorem deHead_ok (s : State) {B : Addr} {Z eA eB eM : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eA) (h17 : s.gpr .x17 = off B eB) (h8 : s.gpr .x8 = off B eM)
    (hA : eA + 8 ≤ Z) (hB : eB + 8 ≤ Z) (hM : eM + 8 ≤ Z)
    (m9 : Msk s .x9 .x4) (m10 : Msk s .x10 .x5) (m19 : Msk s .x19 .x6) (m20 : Msk s .x20 .x7)
    (b1 : Cb59 s .x4 .x5) (b2 : Cb59 s .x6 .x7) :
    WP isa (.block deHead) s fun t =>
      (((t.gpr .x1).toNat : Int) + 2 ^ 64 * ((t.gpr .x13).toInt + (t.gpr .x23).toNat) =
          (s.gpr .x4).toInt * (word s.mem B eA).toNat + (s.gpr .x5).toInt * (word s.mem B eB).toNat +
          (t.gpr .x26).toNat * (word s.mem B eM).toNat ∧
        ((t.gpr .x24).toNat : Int) + 2 ^ 64 * ((t.gpr .x25).toInt + (t.gpr .x30).toNat) =
          (s.gpr .x6).toInt * (word s.mem B eA).toNat + (s.gpr .x7).toInt * (word s.mem B eB).toNat +
          (t.gpr .x27).toNat * (word s.mem B eM).toNat ∧
        (t.gpr .x13).toInt.natAbs ≤ 2 ^ 61 ∧ (t.gpr .x25).toInt.natAbs ≤ 2 ^ 61 ∧
        t.gpr .x26 = (s.gpr .x4 * word s.mem B eA + s.gpr .x5 * word s.mem B eB) * s.gpr .x28 ∧
        t.gpr .x27 = (s.gpr .x6 * word s.mem B eA + s.gpr .x7 * word s.mem B eB) * s.gpr .x28 ∧
        t.gpr .x28 = 0#64 ∧ t.mem = s.mem) ∧
      Keep [.x1, .x2, .x3, .x13, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x30] s t := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  unfold deHead deRow prodsD carryIn kterm
  brun [h16, h17, h8, hs.ld hA, hs.ld hB, hs.ld hM, exec_sbc_x, exec_madd_x]
  have r1 := deRowValUD (s.gpr .x4) (s.gpr .x5) (word s.mem B eA) (word s.mem B eB) 0#64
    ((s.gpr .x4 * word s.mem B eA + s.gpr .x5 * word s.mem B eB) * s.gpr .x28) (word s.mem B eM) 0#64 b1 (by decide)
  have r2 := deRowValUD (s.gpr .x6) (s.gpr .x7) (word s.mem B eA) (word s.mem B eB) 0#64
    ((s.gpr .x6 * word s.mem B eA + s.gpr .x7 * word s.mem B eB) * s.gpr .x28) (word s.mem B eM) 0#64 b2 (by decide)
  rw [m9, m10, m19, m20]
  simp only [show BitVec.setWidth 64 0#16 = 0#64 from rfl, Bool.toNat_false, BitVec.add_zero, Nat.add_zero, word,
    BitVec.toInt_zero, BitVec.toNat_zero, Int.add_zero, Int.natCast_zero] at r1 r2 ⊢
  exact ⟨r1.1, r2.1, r1.2, r2.2⟩

/-- Word `n` of a row over `(a, b)`: `rowWord`, then `+ kc`. -/
theorem deTopVal (cu cv a b c kc : BitVec 64) (hb : cu.toInt.natAbs + cv.toInt.natAbs ≤ 2 ^ 59)
    (hc : c.toInt.natAbs ≤ 2 ^ 61) :
    let lo1 := cu * a
    let hi1 := BitVec.ofNat 64 (cu.toNat * a.toNat / 2 ^ 64) - (a &&& (0#64 - (cu >>> 63)))
    let lo2 := cv * b
    let hi2 := BitVec.ofNat 64 (cv.toNat * b.toNat / 2 ^ 64) - (b &&& (0#64 - (cv >>> 63)))
    let s1 := lo1 + lo2
    let lo := s1 + c
    let lo' := lo + kc
    let c'' := hi1 + hi2 + BitVec.ofNat 64 (decide (2 ^ 64 ≤ lo1.toNat + lo2.toNat)).toNat +
      ~~~((c >>> 63) - 1#64) + BitVec.ofNat 64 ((decide (2 ^ 64 ≤ s1.toNat + c.toNat)).toNat +
        (decide (2 ^ 64 ≤ lo.toNat + kc.toNat)).toNat)
    (lo'.toNat : Int) + 2 ^ 64 * c''.toInt = cu.toInt * a.toNat + cv.toInt * b.toNat + c.toInt + kc.toNat ∧
      c''.toInt.natAbs ≤ 2 ^ 61 := by
  intro lo1 hi1 lo2 hi2 s1 lo lo' c''
  let c' := hi1 + hi2 + BitVec.ofNat 64 (decide (2 ^ 64 ≤ lo1.toNat + lo2.toNat)).toNat +
    ~~~((c >>> 63) - 1#64) + BitVec.ofNat 64 (decide (2 ^ 64 ≤ s1.toNat + c.toNat)).toNat
  obtain ⟨r1, -⟩ := Divstep.rowWord cu cv a b c (by omega) (by omega)
  have cb : c'.toInt.natAbs ≤ 2 ^ 59 + 1 :=
    carry_bound lo.isLt r1 (lin_abs cu cv _ _ _ a.isLt b.isLt hb hc)
  have ec : c'' = c' + BitVec.ofNat 64 (decide (2 ^ 64 ≤ lo.toNat + kc.toNat)).toNat := by
    simp only [c'', c', BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hC : (decide (2 ^ 64 ≤ lo.toNat + kc.toNat)).toNat ≤ 1 := Bool.toNat_le _
  have tc : c''.toInt = c'.toInt + (decide (2 ^ 64 ≤ lo.toNat + kc.toNat)).toNat := by
    rw [ec]; exact toInt_add_bit _ _ hC cb
  refine ⟨?_, by rw [tc]; exact natAbs_add_bit hC cb⟩
  rw [tc]
  have r1' : (lo.toNat : Int) + 2 ^ 64 * c'.toInt = cu.toInt * a.toNat + cv.toInt * b.toNat + c.toInt := r1
  have hl : lo'.toNat = (lo.toNat + kc.toNat) % 2 ^ 64 := by simp only [lo', BitVec.toNat_add]
  have d := Divstep.decide_toNat_div (lo.toNat + kc.toNat) (by have := lo.isLt; have := kc.isLt; omega)
  rw [hl, d]
  have := Nat.div_add_mod (lo.toNat + kc.toNat) (2 ^ 64)
  omega

/-- `deTopVal` for `prodsD`. -/
theorem deTopValD (cu cv a b c kc : BitVec 64) (hb : cu.toInt.natAbs + cv.toInt.natAbs ≤ 2 ^ 59)
    (hc : c.toInt.natAbs ≤ 2 ^ 61) :
    let s1 := cu * a + cv * b
    let lo := s1 + c
    let lo' := lo + kc
    let c'' := off (off (BitVec.ofNat 64 (cu.toNat * a.toNat / 2 ^ 64))
        (cv.toNat * b.toNat / 2 ^ 64 + (decide (2 ^ 64 ≤ (cu * a).toNat + (cv * b).toNat)).toNat) -
          (a &&& 0#64 - cu >>> 63) - (b &&& 0#64 - cv >>> 63) + ~~~(c >>> 63 - 1#64))
        ((decide (2 ^ 64 ≤ s1.toNat + c.toNat)).toNat + (decide (2 ^ 64 ≤ lo.toNat + kc.toNat)).toNat)
    (lo'.toNat : Int) + 2 ^ 64 * c''.toInt = cu.toInt * a.toNat + cv.toInt * b.toNat + c.toInt + kc.toNat ∧
      c''.toInt.natAbs ≤ 2 ^ 61 := by
  intro s1 lo lo' c''
  have e : c'' = BitVec.ofNat 64 (cu.toNat * a.toNat / 2 ^ 64) - (a &&& (0#64 - (cu >>> 63))) +
      (BitVec.ofNat 64 (cv.toNat * b.toNat / 2 ^ 64) - (b &&& (0#64 - (cv >>> 63)))) +
      BitVec.ofNat 64 (decide (2 ^ 64 ≤ (cu * a).toNat + (cv * b).toNat)).toNat +
      ~~~((c >>> 63) - 1#64) + BitVec.ofNat 64 ((decide (2 ^ 64 ≤ s1.toNat + c.toNat)).toNat +
        (decide (2 ^ 64 ≤ lo.toNat + kc.toNat)).toNat) := by
    simp only [c'', off, ← BitVec.ofNat_add_ofNat, BitVec.sub_eq_add_neg]
    ac_rfl
  rw [e]
  exact deTopVal cu cv a b c kc hb hc

/-- The code of the end of the pass over `(a, b)`. -/
def deTail : List Instr := deTop ++ topFix .x13 .x4 .x5 ++ topFix .x25 .x6 .x7 ++ [st .x13 .x16, st .x25 .x17]

/-- The end of the pass over `(a, b)`: word `n` of the rows (`m`'s not read),
the carries corrected for the top words' signs, and both written. -/
theorem deTail_ok (s : State) {B : Addr} {Z eA eB : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eA) (h17 : s.gpr .x17 = off B eB) (hA : eA + 16 ≤ Z) (hB : eB + 16 ≤ Z)
    (h28 : s.gpr .x28 = 0#64)
    (m9 : Msk s .x9 .x4) (m10 : Msk s .x10 .x5) (m19 : Msk s .x19 .x6) (m20 : Msk s .x20 .x7)
    (b1 : Cb59 s .x4 .x5) (b2 : Cb59 s .x6 .x7) (c1 : (s.gpr .x13).toInt.natAbs ≤ 2 ^ 61)
    (c2 : (s.gpr .x25).toInt.natAbs ≤ 2 ^ 61) :
    WP isa (.block deTail) s fun t => ∃ lo₁ lo₂ c₁ c₂ : BitVec 64,
      t.mem = (((s.mem.writeW (off B eA) lo₁).writeW (off B eB) lo₂).writeW (off B (eA + 8)) c₁).writeW
        (off B (eB + 8)) c₂ ∧
      (lo₁.toNat : Int) + 2 ^ 64 * (c₁.toInt +
          (if (word s.mem B (eA + 8)).toNat < 2 ^ 63 then 0 else (s.gpr .x4).toInt) +
          (if (word s.mem B (eB + 8)).toNat < 2 ^ 63 then 0 else (s.gpr .x5).toInt)) =
        (s.gpr .x4).toInt * (word s.mem B (eA + 8)).toNat + (s.gpr .x5).toInt * (word s.mem B (eB + 8)).toNat +
        (s.gpr .x13).toInt + (s.gpr .x23).toNat ∧
      (lo₂.toNat : Int) + 2 ^ 64 * (c₂.toInt +
          (if (word s.mem B (eA + 8)).toNat < 2 ^ 63 then 0 else (s.gpr .x6).toInt) +
          (if (word s.mem B (eB + 8)).toNat < 2 ^ 63 then 0 else (s.gpr .x7).toInt)) =
        (s.gpr .x6).toInt * (word s.mem B (eA + 8)).toNat + (s.gpr .x7).toInt * (word s.mem B (eB + 8)).toNat +
        (s.gpr .x25).toInt + (s.gpr .x30).toNat := by
  unfold deTail deTop deRowTop prodsD carryIn topFix
  brun [h16, h17, h28, hs.ld (show eA + 8 + 8 ≤ Z by omega_arith), hs.ld (show eB + 8 + 8 ≤ Z by omega_arith),
    hs.st (show eA + 8 ≤ Z by omega_arith), hs.st (show eB + 8 ≤ Z by omega_arith),
    hs.st (show eA + 8 + 8 ≤ Z by omega_arith), hs.st (show eB + 8 + 8 ≤ Z by omega_arith), exec_sbc_x,
    BitVec.add_zero, show BitVec.setWidth 64 0#16 = 0#64 from rfl]
  have r1 := deTopValD (s.gpr .x4) (s.gpr .x5) (word s.mem B (eA + 8)) (word s.mem B (eB + 8)) (s.gpr .x13)
    (s.gpr .x23) b1 c1
  have r2 := deTopValD (s.gpr .x6) (s.gpr .x7) (word s.mem B (eA + 8)) (word s.mem B (eB + 8)) (s.gpr .x25)
    (s.gpr .x30) b2 c2
  rw [m9, m10, m19, m20]
  simp only [Bool.toNat_false, BitVec.add_zero, Nat.add_zero, word] at r1 r2 ⊢
  refine ⟨_, _, _, _, rfl, ?_, ?_⟩
  · rw [topFixVal _ _ _ _ _ (Nat.le_trans r1.2 (by decide)) b1]
    have := r1.1
    omega
  · rw [topFixVal _ _ _ _ _ (Nat.le_trans r2.2 (by decide)) b2]
    have := r2.1
    omega

/-- The end of a row over `(a, b)`: the words written, after the low word
`s0`, are `(u a + v b + k M) / 2^64` modulo `2^(64 (n + 1))`. -/
theorem deFinal {N s0 O lo A B M an bn k : Nat} {c kc u v : Int} {c₁ : BitVec 64}
    (hv : ((s0 + 2 ^ 64 * O : Nat) : Int) + ((2 ^ (64 * N) * 2 ^ 64 : Nat) : Int) * (c + kc) = u * A + v * B + k * M)
    (hw : (lo : Int) + 2 ^ 64 * (c₁.toInt + (if an < 2 ^ 63 then 0 else u) + (if bn < 2 ^ 63 then 0 else v)) =
      u * an + v * bn + c + kc)
    (hsA : Divstep.sgn (N + 1 + 1) (A + 2 ^ (64 * N) * 2 ^ 64 * an) =
      ((A + 2 ^ (64 * N) * 2 ^ 64 * an : Nat) : Int) - (if an < 2 ^ 63 then 0 else ((2 ^ (64 * N) * 2 ^ 64 * 2 ^ 64 : Nat) : Int)))
    (hsB : Divstep.sgn (N + 1 + 1) (B + 2 ^ (64 * N) * 2 ^ 64 * bn) =
      ((B + 2 ^ (64 * N) * 2 ^ 64 * bn : Nat) : Int) - (if bn < 2 ^ 63 then 0 else ((2 ^ (64 * N) * 2 ^ 64 * 2 ^ 64 : Nat) : Int))) :
    ∃ e : Int, (s0 : Int) + 2 ^ 64 * (((O + 2 ^ (64 * N) * lo + 2 ^ (64 * N) * 2 ^ 64 * c₁.toNat : Nat) : Int) +
      ((2 ^ (64 * N) * 2 ^ 64 * 2 ^ 64 : Nat) : Int) * e) =
      u * Divstep.sgn (N + 1 + 1) (A + 2 ^ (64 * N) * 2 ^ 64 * an) +
        v * Divstep.sgn (N + 1 + 1) (B + 2 ^ (64 * N) * 2 ^ 64 * bn) + k * M := by
  obtain ⟨b, hb, tn⟩ : ∃ b : Int, (b = 0 ∨ b = 1) ∧ (c₁.toNat : Int) = c₁.toInt + 2 ^ 64 * b := by
    rw [BitVec.toInt_eq_toNat_cond]
    split
    · exact ⟨0, .inl rfl, by omega⟩
    · exact ⟨1, .inr rfl, by omega⟩
  rw [show (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) by rw [Int.natCast_pow]; rfl] at tn hw ⊢
  rw [hsA, hsB]
  refine ⟨-b, ?_⟩
  generalize 2 ^ (64 * N) = P at *
  generalize 2 ^ 64 = Q at *
  have := congrArg (fun z => (P : Int) * Q * z) hw
  clear hsA hsB
  generalize c₁.toNat = cn at *
  generalize c₁.toInt = ci at *
  by_cases ha : an < 2 ^ 63 <;> by_cases hb' : bn < 2 ^ 63 <;>
  · simp only [ha, hb', ite_true, ite_false] at this ⊢
    clear hw
    push_cast at hv this tn ⊢
    have t2 : (P : Int) * Q * Q * cn = P * Q * Q * (ci + Q * b) := by rw [tn]
    grind

/-- The start of the pass over `(a, b)`: `-m⁻¹` from its lane, the arrays'
addresses, and `x14 := n - 1`. -/
theorem deStart_ok {s : State} {B : Addr} {w : Nat} (iA iB iM : Nat) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) :
    WP isa (.block (([.umov .x .x28 .v18 1] : List Instr) ++ base iA .x16 ++ base iB .x17 ++ base iM .x8 ++
      ([.subImm .x .x14 .x12 1] : List Instr))) s fun t =>
      (t.gpr .x28 = laneOf s .v18 1 ∧ t.gpr .x16 = off B (slot w iA) ∧ t.gpr .x17 = off B (slot w iB) ∧
        t.gpr .x8 = off B (slot w iM) ∧ t.gpr .x14 = s.gpr .x12 - 1#64 ∧ t.mem = s.mem) ∧
      Keep [.x28, .x16, .x17, .x8, .x14] s t := by
  rw [show ([Instr.umov .x .x28 .v18 1] ++ base iA .x16 ++ base iB .x17 ++ base iM .x8 ++ [.subImm .x .x14 .x12 1]) =
      [Instr.umov .x .x28 .v18 1] ++ ((base iA .x16 ++ base iB .x17 ++ base iM .x8) ++ [.subImm .x .x14 .x12 1]) by simp,
    WP.block_append_iff]
  refine WP.mono (WP.keep [.x28] (Q := fun t => t.gpr .x28 = laneOf s .v18 1 ∧ t.mem = s.mem)
    (by brun [exec_umov (show 1 < 2 by decide)]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h28, m₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base3_ok iA iB iM .x16 .x17 .x8 ((k₁.gpr .x0 (by decide)).trans h0)
    ((k₁.gpr .x11 (by decide)).trans h11)) fun s₂ ⟨⟨h16, h17, h8, m₂, _⟩, k₂⟩ => ?_
  refine WP.mono (WP.keep [.x14] (Q := fun t => t.gpr .x14 = s₂.gpr .x12 - 1#64 ∧ t.mem = s₂.mem)
    (by brun) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h14, m₃⟩, k₃⟩ => ?_
  refine ⟨⟨(k₃.gpr .x28 (by decide)).trans ((k₂.gpr .x28 (by decide)).trans h28),
    (k₃.gpr .x16 (by decide)).trans h16, (k₃.gpr .x17 (by decide)).trans h17, (k₃.gpr .x8 (by decide)).trans h8,
    by rw [h14, k₂.gpr .x12 (by decide), k₁.gpr .x12 (by decide)], by rw [m₃, m₂, m₁]⟩,
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- `x30` into lane 0 of `v25`. -/
def deKs : List (Reg × VReg × Nat) := [(.x30, .v25, 0)]

/-- The loop of the pass over `(a, b)`: words `1` to `n - 1`, if any. -/
theorem deLoop_ok {s₃ : State} {B : Addr} {Z N eA eB eM : Nat} (h14 : s₃.gpr .x14 = BitVec.ofNat 64 N)
    (hN : N < 2 ^ 32) (h28 : s₃.gpr .x28 = 0#64)
    (m9 : Msk s₃ .x9 .x4) (m10 : Msk s₃ .x10 .x5) (m19 : Msk s₃ .x19 .x6) (m20 : Msk s₃ .x20 .x7)
    (b1 : Cb59 s₃ .x4 .x5) (b2 : Cb59 s₃ .x6 .x7) (hA : eA + 8 * (N + 1 + 1) ≤ Z) (hB : eB + 8 * (N + 1 + 1) ≤ Z)
    (hM : eM + 8 * (N + 1 + 1) ≤ Z) (sep : eA + 8 * (N + 1 + 1) ≤ eB ∨ eB + 8 * (N + 1 + 1) ≤ eA)
    (sAM : eA + 8 * (N + 1 + 1) ≤ eM ∨ eM + 8 * (N + 1 + 1) ≤ eA)
    (sBM : eB + 8 * (N + 1 + 1) ≤ eM ∨ eM + 8 * (N + 1 + 1) ≤ eB) (I0 : DeInv s₃ B Z eA eB eM 0 s₃) :
    WP isa (.ite (.zero .x .x14) (.block []) (countLoop .x14 deBody)) s₃ (DeInv s₃ B Z eA eB eM N) := by
  refine WP.ite (s₃.gpr .x14 == 0) (VG.Proof.MlKem.AArch64.eval_zero _ _) (fun hz => ?_) (fun hnz => ?_)
  · have : N = 0 := by
      rw [h14] at hz
      have := congrArg BitVec.toNat (beq_iff_eq.mp hz)
      simp at this; omega
    subst this
    exact WP.block_nil I0
  · have hN0 : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · subst h; rw [h14] at hnz; simp at hnz
      · exact h
    exact wp_countdown (N := N) (by omega) hN0 (DeInv s₃ B Z eA eB eM)
      (fun j hj t hI _ => deStep_ok (n := N + 1) h28 m9 m10 m19 m20 b1 b2 hA hB hM sep sAM sBM (by omega) hI) I0 h14

/-- The end of the pass over `(a, b)`: word `n`, and `x30` back from its
lane; the rows' sums from the loop's invariant. -/
theorem deEnd_ok {s₃ u : State} {B : Addr} {Z N eA eB eM : Nat} (hI : DeInv s₃ B Z eA eB eM N u)
    (h28 : s₃.gpr .x28 = 0#64)
    (m9 : Msk s₃ .x9 .x4) (m10 : Msk s₃ .x10 .x5) (m19 : Msk s₃ .x19 .x6) (m20 : Msk s₃ .x20 .x7)
    (b1 : Cb59 s₃ .x4 .x5) (b2 : Cb59 s₃ .x6 .x7) (hA : eA + 8 * (N + 1 + 1) ≤ Z) (hB : eB + 8 * (N + 1 + 1) ≤ Z)
    (sep : eA + 8 * (N + 1 + 1) ≤ eB ∨ eB + 8 * (N + 1 + 1) ≤ eA) :
    WP isa (.seq (.block deTail) (.block (umovOf deKs))) u fun t =>
      (∃ s0 : Nat, s0 < 2 ^ 64 ∧ ∃ e : Int, (s0 : Int) + 2 ^ 64 * ((wv t.mem B eA (N + 1 + 1) : Int) +
          ((2 ^ (64 * (N + 1 + 1)) : Nat) : Int) * e) =
        (s₃.gpr .x4).toInt * Divstep.sgn (N + 1 + 1) (wv s₃.mem B eA (N + 1 + 1)) +
        (s₃.gpr .x5).toInt * Divstep.sgn (N + 1 + 1) (wv s₃.mem B eB (N + 1 + 1)) +
        (s₃.gpr .x26).toNat * wv s₃.mem B eM (N + 1)) ∧
      (∃ s0 : Nat, s0 < 2 ^ 64 ∧ ∃ e : Int, (s0 : Int) + 2 ^ 64 * ((wv t.mem B eB (N + 1 + 1) : Int) +
          ((2 ^ (64 * (N + 1 + 1)) : Nat) : Int) * e) =
        (s₃.gpr .x6).toInt * Divstep.sgn (N + 1 + 1) (wv s₃.mem B eA (N + 1 + 1)) +
        (s₃.gpr .x7).toInt * Divstep.sgn (N + 1 + 1) (wv s₃.mem B eB (N + 1 + 1)) +
        (s₃.gpr .x27).toNat * wv s₃.mem B eM (N + 1)) ∧
      Frm B [(eA, 8 * (N + 1 + 1)), (eB, 8 * (N + 1 + 1))] s₃.mem t.mem ∧
      Keep [.x1, .x2, .x3, .x8, .x13, .x14, .x16, .x17, .x21, .x22, .x23, .x24, .x25, .x30] s₃ t ∧
      t.gpr .x30 = laneOf u .v25 0 ∧ t.v = u.v := by
  have hn := hI.scr.nowrap
  have ku : ∀ r : Reg, r ∉ [.x1, .x2, .x3, .x8, .x13, .x14, .x16, .x17, .x21, .x22, .x23, .x24, .x25, .x30] →
      u.gpr r = s₃.gpr r := fun r hr => hI.keep.gpr r hr
  refine WP.seq (WP.mono (WP.vfix (WP.keep [.x1, .x2, .x3, .x13, .x16, .x17, .x21, .x22, .x23, .x24, .x25]
    (deTail_ok u (eA := eA + 8 * N) (eB := eB + 8 * N) hI.scr hI.x16 hI.x17 (by omega_arith)
      (by omega_arith) (by rw [ku _ (by decide)]; exact h28)
      (by unfold Msk; rw [ku _ (by decide), ku _ (by decide), m9]) (by unfold Msk; rw [ku _ (by decide), ku _ (by decide), m10])
      (by unfold Msk; rw [ku _ (by decide), ku _ (by decide), m19]) (by unfold Msk; rw [ku _ (by decide), ku _ (by decide), m20])
      (by unfold Cb59; rw [ku _ (by decide), ku _ (by decide)]; exact b1)
      (by unfold Cb59; rw [ku _ (by decide), ku _ (by decide)]; exact b2) hI.c₁ hI.c₂)
    (by decide) (by decide) (by decide +kernel)) (by decide))
    fun t₁ ⟨⟨⟨lo₁, lo₂, c₁', c₂', hmt, hw1, hw2⟩, kt⟩, vt⟩ => ?_)
  refine WP.mono (WP.vfix (show WP isa (.block (umovOf deKs)) t₁ _ from umovOf_ok deKs t₁ (by decide) (by decide))
    (by decide)) fun t ⟨⟨mt, rdt, wrt, spt, rest, oth⟩, vt'⟩ => ?_
  -- The top words read are the first ones'.
  have rA : word u.mem B (eA + 8 * N + 8) = word s₃.mem B (eA + 8 * N + 8) :=
    hI.frm.word_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith)
      (by omega_arith)
  have rB : word u.mem B (eB + 8 * N + 8) = word s₃.mem B (eB + 8 * N + 8) :=
    hI.frm.word_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith)
      (by omega_arith)
  obtain ⟨wa₁, wb₁⟩ := wv_write2 u.mem B lo₁ lo₂ (eF := eA) (eG := eB) (j := N) (by omega_arith)
    (by omega_arith) (by omega_arith)
  obtain ⟨wa₂, wb₂⟩ := wv_write2 ((u.mem.writeW (off B (eA + 8 * N)) lo₁).writeW (off B (eB + 8 * N)) lo₂)
    B c₁' c₂' (eF := eA) (eG := eB) (j := N + 1) (by omega_arith) (by omega_arith) sep
  rw [show eA + 8 * (N + 1) = eA + 8 * N + 8 by omega_arith,
    show eB + 8 * (N + 1) = eB + 8 * N + 8 by omega_arith] at wa₂ wb₂
  have hmt' : t.mem = (((u.mem.writeW (off B (eA + 8 * N)) lo₁).writeW (off B (eB + 8 * N)) lo₂).writeW
      (off B (eA + 8 * N + 8)) c₁').writeW (off B (eB + 8 * N + 8)) c₂' := mt.trans hmt
  have tW : ∀ e, wv s₃.mem B e (N + 1 + 1) = wv s₃.mem B e (N + 1) +
      2 ^ (64 * N) * 2 ^ 64 * (word s₃.mem B (e + 8 * N + 8)).toNat := fun e => by
    rw [wv, pow64_succ, show e + 8 * (N + 1) = e + 8 * N + 8 by omega_arith]
  have sg : ∀ e, Divstep.sgn (N + 1 + 1) (wv s₃.mem B e (N + 1) + 2 ^ (64 * N) * 2 ^ 64 *
      (word s₃.mem B (e + 8 * N + 8)).toNat) =
      ((wv s₃.mem B e (N + 1) + 2 ^ (64 * N) * 2 ^ 64 * (word s₃.mem B (e + 8 * N + 8)).toNat : Nat) : Int) -
        (if (word s₃.mem B (e + 8 * N + 8)).toNat < 2 ^ 63 then 0 else ((2 ^ (64 * N) * 2 ^ 64 * 2 ^ 64 : Nat) : Int)) :=
    fun e => by
      have := sgn_top (n := N + 1) (wv_lt s₃.mem B e (N + 1)) (word s₃.mem B (e + 8 * N + 8)).isLt
      rw [pow64_succ] at this
      exact this
  have p2 : ((2 ^ (64 * (N + 1 + 1)) : Nat) : Int) = ((2 ^ (64 * N) * 2 ^ 64 * 2 ^ 64 : Nat) : Int) := by
    rw [pow64_succ, pow64_succ]
  have kt' : Keep [.x1, .x2, .x3, .x8, .x13, .x14, .x16, .x17, .x21, .x22, .x23, .x24, .x25, .x30]
      s₃ t := by
    refine ⟨fun r hr => ?_, rdt.trans (kt.rd.trans hI.keep.rd), wrt.trans (kt.wr.trans hI.keep.wr),
      spt.trans (kt.sp.trans hI.keep.sp), fun r hr => ?_⟩
    · have m1 : ∀ r : Reg, r ∉ [.x1, .x2, .x3, .x8, .x13, .x14, .x16, .x17, .x21, .x22, .x23, .x24, .x25, .x30] →
          r ∉ deKs.map Prod.fst ∧ r ∉ [.x1, .x2, .x3, .x13, .x16, .x17, .x21, .x22, .x23, .x24, .x25] ∧
          r ∉ [.x1, .x2, .x3, .x8, .x13, .x14, .x16, .x17, .x21, .x22, .x23, .x24, .x25, .x30] := by
        intro r; cases r <;> decide
      obtain ⟨a1, a2, a3⟩ := m1 r hr
      rw [oth r a1, kt.gpr r a2, ku r a3]
    · rw [vt', vt]; exact hI.keep.vcs r hr
  have ln : ∀ (v : VReg) (l : Nat), laneOf t₁ v l = laneOf u v l := fun v l => by unfold laneOf; rw [vt]
  refine ⟨?_, ?_, ?_, kt', by rw [rest (.x30, .v25, 0) (by decide), ln], vt'.trans vt⟩
  · obtain ⟨s0, hs0, hv⟩ := hI.v₁
    refine ⟨s0, hs0, ?_⟩
    rw [hmt', wa₂, wa₁, p2, tW, tW, pow64_succ]
    rw [rA, rB, ku .x4 (by decide), ku .x5 (by decide)] at hw1
    exact deFinal hv hw1 (sg _) (sg _)
  · obtain ⟨s0, hs0, hv⟩ := hI.v₂
    refine ⟨s0, hs0, ?_⟩
    rw [hmt', wb₂, wb₁, p2, tW, tW, pow64_succ]
    rw [rA, rB, ku .x6 (by decide), ku .x7 (by decide)] at hw2
    exact deFinal hv hw2 (sg _) (sg _)
  · rw [hmt']
    have f1 := Frm.write2 hI.frm lo₁ lo₂ (by omega_arith) (by omega_arith)
    have f2 := Frm.write2 f1 c₁' c₂' (j := N + 1) (by omega_arith) (by omega_arith)
    rw [show eA + 8 * (N + 1) = eA + 8 * N + 8 by omega_arith,
      show eB + 8 * (N + 1) = eB + 8 * N + 8 by omega_arith] at f2
    exact f2

/-- `dePass a b m`: `(a, b) := ((u a + v b + k₁ m) / 2^64, (q a + r b + k₂ m) / 2^64)`
modulo `2^(64 (n + 1))`, `a`, `b` signed numbers of `n + 1` words, `m` of
`n`, and `kᵢ` from the rows' low words and `-m⁻¹` (lane 1 of `v18`): the low
word `s0` of each sum, and the words above it. -/
theorem dePass_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hn1 : 1 ≤ n) (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iA iB iM : Nat}
    (hA : iA < 16) (hB : iB < 16) (hM : iM < 16) (dAB : iA ≠ iB) (dAM : iA ≠ iM) (dBM : iB ≠ iM)
    (m9 : Msk s .x9 .x4) (m10 : Msk s .x10 .x5) (m19 : Msk s .x19 .x6) (m20 : Msk s .x20 .x7)
    (b1 : Cb59 s .x4 .x5) (b2 : Cb59 s .x6 .x7) :
    WP isa (dePass iA iB iM) s fun t =>
      (∃ s0 : Nat, s0 < 2 ^ 64 ∧ ∃ e : Int, (s0 : Int) + 2 ^ 64 * ((wv t.mem B (slot w iA) (n + 1) : Int) +
          ((2 ^ (64 * (n + 1)) : Nat) : Int) * e) =
        (s.gpr .x4).toInt * Divstep.sgn (n + 1) (wv s.mem B (slot w iA) (n + 1)) +
        (s.gpr .x5).toInt * Divstep.sgn (n + 1) (wv s.mem B (slot w iB) (n + 1)) +
        ((s.gpr .x4 * word s.mem B (slot w iA) + s.gpr .x5 * word s.mem B (slot w iB)) * laneOf s .v18 1).toNat *
          wv s.mem B (slot w iM) n) ∧
      (∃ s0 : Nat, s0 < 2 ^ 64 ∧ ∃ e : Int, (s0 : Int) + 2 ^ 64 * ((wv t.mem B (slot w iB) (n + 1) : Int) +
          ((2 ^ (64 * (n + 1)) : Nat) : Int) * e) =
        (s.gpr .x6).toInt * Divstep.sgn (n + 1) (wv s.mem B (slot w iA) (n + 1)) +
        (s.gpr .x7).toInt * Divstep.sgn (n + 1) (wv s.mem B (slot w iB) (n + 1)) +
        ((s.gpr .x6 * word s.mem B (slot w iA) + s.gpr .x7 * word s.mem B (slot w iB)) * laneOf s .v18 1).toNat *
          wv s.mem B (slot w iM) n) ∧
      Frm B [(slot w iA, 8 * (n + 1)), (slot w iB, 8 * (n + 1))] s.mem t.mem ∧
      Keep [.x1, .x2, .x3, .x8, .x13, .x14, .x16, .x17, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] s t ∧
      ∀ r l, l < 2 → r ≠ .v25 → r ≠ .v26 → laneOf t r l = laneOf s r l := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hn' := hs.nowrap
  have sA := Nat.le_trans (slot_lt (w := w) hA) hZ
  have sB := Nat.le_trans (slot_lt (w := w) hB) hZ
  have sM := Nat.le_trans (slot_lt (w := w) hM) hZ
  have ap : ∀ {i j : Nat}, i ≠ j → slot w i + 8 * (N + 1 + 1) ≤ slot w j ∨ slot w j + 8 * (N + 1 + 1) ≤ slot w i :=
    fun h => by rcases slot_sep (w := w) h with h | h <;> [exact .inl (by omega_arith); exact .inr (by omega_arith)]
  unfold dePass
  refine WP.seq (WP.mono (WP.vfix (deStart_ok iA iB iM h0 h11) (by
      simp only [Code.allInstrs_eq, instrs, List.all_append, base_vnone]; decide))
    fun s₁ ⟨⟨⟨h28, h16, h17, h8, h14, m₁⟩, k₁⟩, v₁⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [] (show WP isa (.block (insOf deKs)) s₁ _ from
    insOf_ok deKs s₁ (by decide) (by decide)) (by decide) (by decide) (by decide +kernel))
    fun s₂ ⟨⟨g₂, m₂, _, _, _, l₂, o₂⟩, k₂⟩ => ?_)
  have e₂ : ∀ r, s₂.gpr r = s₁.gpr r := fun r => by rw [g₂]
  have f₁ : ∀ r : Reg, r ∉ [.x28, .x16, .x17, .x8, .x14] → s₂.gpr r = s.gpr r := fun r hr => by
    rw [e₂]; exact k₁.gpr r hr
  refine WP.seq (WP.mono (WP.vfix (deHead_ok s₂ (eA := slot w iA) (eB := slot w iB) (eM := slot w iM)
    (hs.congr (k₁.trans k₂).wr) (by rw [e₂]; exact h16)
    (by rw [e₂]; exact h17) (by rw [e₂]; exact h8) (by omega_arith) (by omega_arith) (by omega_arith)
    (by unfold Msk; rw [f₁ _ (by decide), f₁ _ (by decide), m9])
    (by unfold Msk; rw [f₁ _ (by decide), f₁ _ (by decide), m10])
    (by unfold Msk; rw [f₁ _ (by decide), f₁ _ (by decide), m19])
    (by unfold Msk; rw [f₁ _ (by decide), f₁ _ (by decide), m20])
    (by unfold Cb59; rw [f₁ _ (by decide), f₁ _ (by decide)]; exact b1)
    (by unfold Cb59; rw [f₁ _ (by decide), f₁ _ (by decide)]; exact b2)) (by decide))
    fun s₃ ⟨⟨⟨w₁, w₂, c₁, c₂, h26, h27, z28, m₃⟩, k₃⟩, v₃⟩ => ?_)
  have k₁₃ := (k₁.trans k₂).trans k₃
  have f₃ : ∀ r : Reg, r ∉ [.x1, .x2, .x3, .x13, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x30] →
      s₃.gpr r = s₂.gpr r := fun r hr => k₃.gpr r hr
  have hm₃ : s₃.mem = s.mem := m₃.trans (m₂.trans m₁)
  have h14' : s₃.gpr .x14 = BitVec.ofNat 64 N := by
    rw [f₃ _ (by decide), e₂, h14, h12]; exact BitVec.eq_of_toNat_eq (by simp; omega)
  have I0 : DeInv s₃ B Z (slot w iA) (slot w iB) (slot w iM) 0 s₃ := by
    refine ⟨hs.congr k₁₃.wr, Keep.refl _ _, by rw [f₃ _ (by decide), e₂, h16]; rfl,
      by rw [f₃ _ (by decide), e₂, h17]; rfl, by rw [f₃ _ (by decide), e₂, h8]; rfl, Frm.refl _ _ _,
      ⟨(s₃.gpr .x1).toNat, (s₃.gpr .x1).isLt, ?_⟩, ⟨(s₃.gpr .x24).toNat, (s₃.gpr .x24).isLt, ?_⟩, c₁, c₂⟩
    · simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
      rw [m₃, f₃ .x4 (by decide), f₃ .x5 (by decide), show ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 by
        rw [Int.natCast_pow]; rfl]
      push_cast at w₁ ⊢
      exact w₁
    · simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
      rw [m₃, f₃ .x6 (by decide), f₃ .x7 (by decide), show ((2 ^ 64 : Nat) : Int) = (2 : Int) ^ 64 by
        rw [Int.natCast_pow]; rfl]
      push_cast at w₂ ⊢
      exact w₂
  have q : ∀ r : Reg, r ∈ [.x0, .x4, .x5, .x6, .x7, .x9, .x10, .x19, .x20] → s₃.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (f₃ _ (by decide)).trans ((e₂ _).trans (k₁.gpr _ (by decide)))
  have M9 : Msk s₃ .x9 .x4 := by unfold Msk; rw [q _ (by decide), q _ (by decide), m9]
  have M10 : Msk s₃ .x10 .x5 := by unfold Msk; rw [q _ (by decide), q _ (by decide), m10]
  have M19 : Msk s₃ .x19 .x6 := by unfold Msk; rw [q _ (by decide), q _ (by decide), m19]
  have M20 : Msk s₃ .x20 .x7 := by unfold Msk; rw [q _ (by decide), q _ (by decide), m20]
  have B1 : Cb59 s₃ .x4 .x5 := by unfold Cb59; rw [q _ (by decide), q _ (by decide)]; exact b1
  have B2 : Cb59 s₃ .x6 .x7 := by unfold Cb59; rw [q _ (by decide), q _ (by decide)]; exact b2
  refine WP.seq (WP.mono (WP.vfix (deLoop_ok h14' (by omega_arith) z28 M9 M10 M19 M20 B1 B2 (by omega_arith)
    (by omega_arith) (by omega_arith) (ap dAB) (ap dAM) (ap dBM) I0) (by decide)) fun u ⟨hI, vu⟩ => ?_)
  refine WP.mono (deEnd_ok hI z28 M9 M10 M19 M20 B1 B2 (by omega_arith) (by omega_arith) (ap dAB))
    fun t ⟨r1, r2, fr, kt, t30, tv⟩ => ?_
  have hk : ∀ c₁ c₂ : Reg, c₁ ∈ [.x4, .x5, .x6, .x7] → c₂ ∈ [.x4, .x5, .x6, .x7] →
      (s₂.gpr c₁ * word s₂.mem B (slot w iA) + s₂.gpr c₂ * word s₂.mem B (slot w iB)) * s₂.gpr .x28 =
      (s.gpr c₁ * word s.mem B (slot w iA) + s.gpr c₂ * word s.mem B (slot w iB)) * laneOf s .v18 1 := by
    intro c₁ c₂ h₁ h₂
    have e : ∀ c : Reg, c ∈ [.x4, .x5, .x6, .x7] → s₂.gpr c = s.gpr c := by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> exact f₁ _ (by decide)
    rw [e c₁ h₁, e c₂ h₂, m₂, m₁, e₂, h28]
  have lnS : ∀ r l, l < 2 → r ≠ .v25 → r ≠ .v26 → laneOf s₂ r l = laneOf s r l := fun r l hl a _ => by
    rw [o₂ r l hl (by simp [deKs, a])]; unfold laneOf; rw [v₁]
  refine ⟨?_, ?_, by rw [← hm₃]; exact fr, ?_, fun r l hl a b => ?_⟩
  · obtain ⟨s0, hs0, e, he⟩ := r1
    refine ⟨s0, hs0, e, ?_⟩
    rw [hm₃, q .x4 (by decide), q .x5 (by decide), h26, hk .x4 .x5 (by decide) (by decide)] at he
    exact he
  · obtain ⟨s0, hs0, e, he⟩ := r2
    refine ⟨s0, hs0, e, ?_⟩
    rw [hm₃, q .x6 (by decide), q .x7 (by decide), h27, hk .x6 .x7 (by decide) (by decide)] at he
    exact he
  · -- `x30` back from its lane, the rest kept.
    have lu : ∀ v l, laneOf u v l = laneOf s₂ v l := fun v l => by unfold laneOf; rw [vu, v₃]
    refine ⟨fun r hr => ?_, kt.rd.trans k₁₃.rd, kt.wr.trans k₁₃.wr, kt.sp.trans k₁₃.sp,
      fun r hr => (kt.vcs r hr).trans (k₁₃.vcs r hr)⟩
    by_cases h₁ : r = .x30
    · subst h₁; rw [t30, lu, l₂ (.x30, .v25, 0) (by decide), k₁.gpr .x30 (by decide)]
    have m1 : ∀ r : Reg, r ∉ [.x1, .x2, .x3, .x8, .x13, .x14, .x16, .x17, .x21, .x22, .x23, .x24, .x25, .x26, .x27,
        .x28] → r ≠ .x30 →
        r ∉ [.x1, .x2, .x3, .x8, .x13, .x14, .x16, .x17, .x21, .x22, .x23, .x24, .x25, .x30] ∧
        r ∉ [.x28, .x16, .x17, .x8, .x14] ++ [] ++
          [.x1, .x2, .x3, .x13, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x30] := by
      intro r; cases r <;> decide
    obtain ⟨a1, a2⟩ := m1 r hr h₁
    rw [kt.gpr r a1, k₁₃.gpr r a2]
  · rw [show laneOf t r l = laneOf s₂ r l by unfold laneOf; rw [tv, vu, v₃], lnS r l hl a b]

end VG.Proof.Rsa.AArch64

-- From `Proof/Rsa/AArch64/InvBase.lean`.
/-!
# RSA private keys on AArch64: what the batched inverse's proofs share

The semantics of the instructions the batched inverse adds to those `brun`
knows (`sbc`, `umov`, `extr`), and the vector registers that code writing
none keeps (`WP.vfix`): `Keys.inverse` keeps `d`, the matrix and the saved
registers in the lanes of `v16`–`v19` across its loops.
-/


namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64

open VG.Impl.Rsa.AArch64.Keys

open VG.Proof.Bignum in
/-- Arrays `j ≠ k` of `w + 2` words: any parts of them are apart. -/
theorem slot_apart {w j k a b : Nat} (h : j ≠ k) (ha : a ≤ 8 * (w + 2)) (hb : b ≤ 8 * (w + 2)) :
    slot w j + a ≤ slot w k ∨ slot w k + b ≤ slot w j := by
  rcases slot_sep (w := w) h with h' | h' <;> [exact .inl (by omega_arith); exact .inr (by omega_arith)]

end VG.Proof.Rsa.AArch64

-- From `Proof/Rsa/AArch64/InvHead.lean`.
/-!
# RSA private keys on AArch64: the start of a batch of divsteps

`batchHead f g` (`batchHead_ok`): `d` from lane 0 of `v18` and the low
words of `f` and `g`, the `59` packed divsteps of the Weierstrass inverse
(`Weierstrass.AArch64.pwords_ok`), and `d` and the matrix into the lanes of
`v18`, `v16`, `v17`. The divsteps leave only `x0`, `x14` and `x15`: the
stride and the width are packed into `x14` across them (`pack_unpack`).
-/


namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.InvBatch
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The stride and the width, packed into a word and back. -/
theorem pack_unpack (S N : Nat) (hS : S < 2 ^ 32) (hN : N < 2 ^ 32) :
    (BitVec.ofNat 64 S <<< 32 + BitVec.ofNat 64 N) >>> 32 = BitVec.ofNat 64 S ∧
    BitVec.ofNat 64 S <<< 32 + BitVec.ofNat 64 N - BitVec.ofNat 64 S <<< 32 = BitVec.ofNat 64 N := by
  refine ⟨?_, by rw [BitVec.add_comm, BitVec.add_sub_cancel]⟩
  rw [shl_ofNat (show S * 2 ^ 32 < 2 ^ 64 by omega_arith), BitVec.ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_arith

/-- The batch head's tail: `d` and the matrix into lanes, `x11`, `x12` back, `x15` counted. -/
theorem headTail_ok' (s : State) {S N : Nat} (hS : S < 2 ^ 32) (hN : N < 2 ^ 32)
    (h14 : s.gpr .x14 = BitVec.ofNat 64 S <<< 32 + BitVec.ofNat 64 N) :
    WP isa (.block (([.vop (.ins .d2 .v18 0 .x1), .vop (.ins .d2 .v16 0 .x4), .vop (.ins .d2 .v16 1 .x5),
      .vop (.ins .d2 .v17 0 .x6), .vop (.ins .d2 .v17 1 .x7)] : List Instr) ++ (unpackW ++ ([.subImm .x .x15 .x15 1] : List Instr)))) s
      fun t => (laneOf t .v18 0 = s.gpr .x1 ∧ laneOf t .v18 1 = laneOf s .v18 1 ∧ laneOf t .v16 0 = s.gpr .x4 ∧
        laneOf t .v16 1 = s.gpr .x5 ∧ laneOf t .v17 0 = s.gpr .x6 ∧ laneOf t .v17 1 = s.gpr .x7 ∧
        (∀ r, r ≠ .v16 → r ≠ .v17 → r ≠ .v18 → t.v r = s.v r) ∧ t.gpr .x11 = BitVec.ofNat 64 S ∧
        t.gpr .x12 = BitVec.ofNat 64 N ∧ t.gpr .x15 = s.gpr .x15 - 1#64 ∧ t.mem = s.mem) ∧
        Keep [.x11, .x12, .x13, .x15] s t := by
  refine WP.keep [.x11, .x12, .x13, .x15] ?_ (by decide) (by decide) (by decide +kernel)
  rw [← List.append_assoc]; unfold unpackW
  brun [exec_ins, h14, RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.v_write, RegUpd.v_setV, (pack_unpack S N hS hN).1]
  simp only [laneOf, RegUpd.v_write, RegUpd.v_setV, (pack_unpack S N hS hN).2]
  simp only [reduceCtorEq, ↓reduceIte, extract_setLane64 _ _ (show (0 : Nat) < 2 by decide) (show (0 : Nat) < 2 by decide), extract_setLane64 _ _ (show (1 : Nat) < 2 by decide) (show (0 : Nat) < 2 by decide), extract_setLane64 _ _ (show (0 : Nat) < 2 by decide) (show (1 : Nat) < 2 by decide), extract_setLane64 _ _ (show (1 : Nat) < 2 by decide) (show (1 : Nat) < 2 by decide), true_and, and_true]
  intro r h1 h2 h3
  simp only [h1, h2, h3, ite_false]

/-- A batch's start: `59` divsteps from `d` (lane 0 of `v18`) and the low
words of `f` and `g` (arrays `iF`, `iG`), and `d` and the matrix into the
lanes of `v18`, `v16` and `v17`. -/
theorem batchHead_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iF iG : Nat} (hF : iF < 16) (hG : iG < 16)
    {d f g : Int} (hd : |d| ≤ 2 ^ 30) (hf : f % 2 = 1) (hv : laneOf s .v18 0 = BitVec.ofInt 64 d)
    (hfw : ((word s.mem B (slot w iF)).toNat : Int) % 2 ^ 64 = f % 2 ^ 64)
    (hgw : ((word s.mem B (slot w iG)).toNat : Int) % 2 ^ 64 = g % 2 ^ 64) :
    WP isa (.block (batchHead iF iG)) s fun t =>
      laneOf t .v18 0 = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init d f g)).d ∧
      laneOf t .v18 1 = laneOf s .v18 1 ∧
      laneOf t .v16 0 = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init d f g)).u ∧
      laneOf t .v16 1 = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init d f g)).v ∧
      laneOf t .v17 0 = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init d f g)).q ∧
      laneOf t .v17 1 = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init d f g)).r ∧
      (∀ r, r ≠ .v16 → r ≠ .v17 → r ≠ .v18 → t.v r = s.v r) ∧ t.gpr .x11 = s.gpr .x11 ∧
      t.gpr .x12 = s.gpr .x12 ∧ t.gpr .x15 = s.gpr .x15 - 1#64 ∧ t.mem = s.mem ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s t := by
  have hn' := hs.nowrap
  have sF := Nat.le_trans (slot_lt (w := w) hF) hZ
  have sG := Nat.le_trans (slot_lt (w := w) hG) hZ
  unfold batchHead
  simp only [List.append_assoc]
  have bv : ∀ j r, (Code.block (base j r) : Prog isa).allInstrs (fun i => (vdstOf i).isNone) = true := fun j r => by
    simp only [Code.allInstrs_eq, instrs, base_vnone]
  refine WP.block_append_iff.mpr (WP.mono (WP.vfix (base_ok iF .x2 h0 h11) (bv _ _)) fun s₁ ⟨⟨⟨h2, m₁, _⟩, k₁⟩, v₁⟩ =>
    WP.block_append_iff.mpr (WP.mono (WP.keep [.x2] (Q := fun t => t.gpr .x2 = word s.mem B (slot w iF) ∧
      t.mem = s₁.mem ∧ t.v = s₁.v) (by brun [h2, m₁, (hs.congr k₁.wr).ld (show slot w iF + 8 ≤ Z by omega_arith), RegUpd.v_write]) (by decide) (by decide)
      (by decide +kernel)) fun s₂ ⟨⟨h2', m₂, v₂⟩, k₂⟩ =>
    WP.block_append_iff.mpr (WP.mono (WP.vfix (base_ok iG .x3 ((k₁.trans k₂ |>.gpr .x0 (by decide)).trans h0)
      ((k₁.trans k₂ |>.gpr .x11 (by decide)).trans h11)) (bv _ _)) fun s₃ ⟨⟨⟨h3, m₃, _⟩, k₃⟩, v₃⟩ => ?_)))
  have k13 := (k₁.trans k₂).trans k₃
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x1, .x3] (Q := fun t => t.gpr .x3 = word s.mem B (slot w iG) ∧
      t.gpr .x1 = laneOf s .v18 0 ∧ t.mem = s₃.mem ∧ t.v = s₃.v)
      (by brun [h3, m₃, m₂, m₁, (hs.congr k13.wr).ld (show slot w iG + 8 ≤ Z by omega_arith), RegUpd.v_write, exec_umov,
        laneOf, v₃, v₂, v₁]) (by decide) (by decide) (by decide +kernel)) fun s₄ ⟨⟨h3', h1', m₄, v₄⟩, k₄⟩ => ?_)
  have k14 := k13.trans k₄
  have e11 : s₄.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) := (k14.gpr .x11 (by decide)).trans h11
  have e12 : s₄.gpr .x12 = BitVec.ofNat 64 n := (k14.gpr .x12 (by decide)).trans h12
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x14] (Q := fun t =>
      t.gpr .x14 = BitVec.ofNat 64 (8 * (w + 2)) <<< 32 + BitVec.ofNat 64 n ∧ t.mem = s₄.mem ∧ t.v = s₄.v)
      (by unfold packW; brun [e11, e12, RegUpd.v_write]) (by decide) (by decide) (by decide +kernel))
    fun s₅ ⟨⟨h14, m₅, v₅⟩, k₅⟩ => ?_)
  have e2 : s₅.gpr .x2 = word s.mem B (slot w iF) := (k₅.gpr .x2 (by decide)).trans ((k₄.gpr .x2 (by decide)).trans
    ((k₃.gpr .x2 (by decide)).trans h2'))
  refine WP.block_append_iff.mpr (WP.mono (WP.vfix (Weierstrass.AArch64.pwords_ok s₅ (g := g) hd hf
    (by rw [k₅.gpr .x1 (by decide), h1', hv]) (by rw [e2]; exact hfw)
    (by rw [k₅.gpr .x3 (by decide), h3']; exact hgw)) (by decide +kernel)) fun s₆ ⟨⟨d₆, u₆, v₆, q₆, r₆, k₆⟩, vv₆⟩ => ?_)
  refine WP.mono (headTail_ok' s₆ (S := 8 * (w + 2)) (N := n) (by omega_arith) (by omega_arith)
    (by rw [k₆.gpr .x14 (by decide)]; exact h14)) fun t ⟨⟨l1, l2, l3, l4, l5, l6, lv, t11, t12, t15, tm⟩, kt⟩ => ?_
  have v06 : s₆.v = s.v := by rw [vv₆, v₅, v₄, v₃, v₂, v₁]
  refine ⟨by rw [l1, d₆], by rw [l2, laneOf, laneOf, v06], by rw [l3, u₆], by rw [l4, v₆], by rw [l5, q₆],
    by rw [l6, r₆], fun r a b c => by rw [lv r a b c, v06], by rw [t11, h11], by rw [t12, h12], ?_, ?_, ?_⟩
  · rw [t15, k₆.gpr .x15 (by decide), k₅.gpr .x15 (by decide), k14.gpr .x15 (by decide)]
  · rw [tm, k₆.mem, m₅, m₄, m₃, m₂, m₁]
  · have k6 : Keep Weierstrass.AArch64.chunkRegs s₅ s₆ := ⟨k₆.gpr, k₆.rd, k₆.wr, k₆.sp, fun r _ => by rw [vv₆]⟩
    exact (((k14.trans k₅).trans k6).trans kt).mono (by decide)
end VG.Proof.Rsa.AArch64

-- From `Proof/Rsa/AArch64/InvStage.lean`.
/-!
# RSA private keys on AArch64: a batch of divsteps after its matrix

With the batch's matrix in the lanes of `v16` and `v17`, the rest of a
batch of `Keys.inverse`: `(f, g) := (u f + v g, q f + r g) / 2^59`
(`fgStage_ok`: two linear combinations, `rowP_ok`, then two shifts,
`shrP_ok`) and `(a, b) := (mredRaw (u a + v b), mredRaw (q a + r b))`
(`abStage_ok`: two linear combinations then two Montgomery words,
`mredP_ok`), as signed numbers of `n + 1` words (`Divstep.sgn`).
-/


namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.InvBatch
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Divstep (sgn)

/-- The values of an array that a piece leaves alone. -/
theorem wv_out {m m' : Mem} {B : Addr} {w o n j L : Nat} (h : Outside B (slot w o) n m m') (hjo : o ≠ j)
    (hn : n ≤ 8 * (w + 2)) (hL : L ≤ w + 2) (hZ : slot w 16 + B.toNat ≤ 2 ^ 64) (hj : j < 16) :
    wv m' B (slot w j) L = wv m B (slot w j) L := by
  have := slot_lt (w := w) hj
  exact h.wv (by rcases slot_apart (w := w) (a := 8 * L) (b := n) hjo.symm (by omega_arith) hn with h' | h' <;> omega_arith) (by omega_arith)

/-- A coefficient pair's bound as the passes take it. -/
theorem cb59_of {u v : Int} {x y : BitVec 64} (hx : x.toInt = u) (hy : y.toInt = v) (huv : |u| + |v| ≤ 2 ^ 59) :
    x.toInt.natAbs + y.toInt.natAbs ≤ 2 ^ 59 := by
  rw [hx, hy]
  have : ((u.natAbs + v.natAbs : Nat) : Int) ≤ 2 ^ 59 := by
    push_cast; exact huv
  exact_mod_cast this

/-- A number of `L` words congruent to `y` modulo `2^(64 L)` is `y`, if `y` fits. -/
theorem sgn_of_cong {L W : Nat} {y e : Int} (hL : 1 ≤ L) (hW : W < 2 ^ (64 * L))
    (hy₀ : -2 ^ (64 * L - 1) ≤ y) (hy₁ : y < 2 ^ (64 * L - 1))
    (h : (W : Int) + ((2 ^ (64 * L) : Nat) : Int) * e = y) : sgn L W = y := by
  refine Divstep.sgn_of_emod hL hy₀ hy₁ ?_
  rw [← h, Divstep.pow64_cast, Int.add_mul_emod_self_left]
  exact (Int.emod_eq_of_lt (by omega_arith) (by have := Divstep.pow64_cast L; exact_mod_cast hW)).symm

/-- The `f`, `g` half of a batch: `(f, g) := (u f + v g, q f + r g) / 2^59`, the
matrix in `x4`–`x7` with its sign masks. -/
theorem fgStage_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hn1 : 1 ≤ n) (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iF iG : Nat}
    (hF : iF < 16) (hG : iG < 16) (dFG : iF ≠ iG)
    {u v q r f g f' g' : Int} (huv : |u| + |v| ≤ 2 ^ 59) (hqr : |q| + |r| ≤ 2 ^ 59)
    (lu : s.gpr .x4 = BitVec.ofInt 64 u) (lv : s.gpr .x5 = BitVec.ofInt 64 v)
    (lq : s.gpr .x6 = BitVec.ofInt 64 q) (lr : s.gpr .x7 = BitVec.ofInt 64 r)
    (m9 : Msk s .x9 .x4) (m10 : Msk s .x10 .x5) (m19 : Msk s .x19 .x6) (m20 : Msk s .x20 .x7)
    (hf : sgn (n + 1) (wv s.mem B (slot w iF) (n + 1)) = f) (hg : sgn (n + 1) (wv s.mem B (slot w iG) (n + 1)) = g)
    (bf : |f| < 2 ^ (64 * n + 1)) (bg : |g| < 2 ^ (64 * n + 1))
    (ef : u * f + v * g = 2 ^ 59 * f') (eg : q * f + r * g = 2 ^ 59 * g') :
    WP isa (fgPass iF iG) s fun t =>
      sgn (n + 1) (wv t.mem B (slot w iF) (n + 1)) = f' ∧ sgn (n + 1) (wv t.mem B (slot w iG) (n + 1)) = g' ∧
      Frm B [(slot w iF, 8 * (n + 1)), (slot w iG, 8 * (n + 1))] s.mem t.mem ∧
      Keep [.x1, .x2, .x3, .x13, .x14, .x16, .x17, .x21, .x22, .x23, .x24, .x25, .x26, .x27] s t ∧ t.v = s.v := by
  obtain ⟨u0, u1, v0, v1, -⟩ := Rsa.Divstep.row_parts huv
  obtain ⟨q0, q1, r0, r1, -⟩ := Rsa.Divstep.row_parts hqr
  have tu : (s.gpr .x4).toInt = u := by rw [lu]; exact Divstep.toInt_ofInt64 (by omega_arith) (by omega_arith)
  have tv : (s.gpr .x5).toInt = v := by rw [lv]; exact Divstep.toInt_ofInt64 (by omega_arith) (by omega_arith)
  have tq : (s.gpr .x6).toInt = q := by rw [lq]; exact Divstep.toInt_ofInt64 (by omega_arith) (by omega_arith)
  have tr : (s.gpr .x7).toInt = r := by rw [lr]; exact Divstep.toInt_ofInt64 (by omega_arith) (by omega_arith)
  obtain ⟨cr10, cr11⟩ := Rsa.Divstep.comb_range huv bf bg
  obtain ⟨cr20, cr21⟩ := Rsa.Divstep.comb_range hqr bf bg
  have hL : (1 : Nat) ≤ n + 1 := by omega_arith
  have hvn : (fgPass iF iG).allInstrs (fun i => (vdstOf i).isNone) = true := by
    simp only [fgPass, Code.allInstrs_eq, instrs, List.all_append, base_vnone]; decide
  refine WP.mono (WP.vfix (fgPass_ok hs h0 h11 h12 hn1 hn hw hZ hF hG dFG m9 m10 m19 m20
    (cb59_of tu tv huv) (cb59_of tq tr hqr) (f' := f') (g' := g')
    (by rw [tu, tv, hf, hg]; exact ef) (by rw [tq, tr, hf, hg]; exact eg)) hvn)
    fun t ⟨⟨⟨e₁, h₁⟩, ⟨e₂, h₂⟩, fr, k⟩, vt⟩ => ⟨?_, ?_, fr, k, vt⟩
  · rw [ef] at cr10 cr11
    exact sgn_of_cong hL (wv_lt _ _ _ _) (by omega_arith) (by omega_arith) h₁
  · rw [eg] at cr20 cr21
    exact sgn_of_cong hL (wv_lt _ _ _ _) (by omega_arith) (by omega_arith) h₂

/-- A frame by smaller ranges is one by larger. -/
theorem Frm.widen {B : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m')
    (hs : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Frm B rs' m m' :=
  fun x hx => h x fun r hr => by
    obtain ⟨r', hr', h1, h2⟩ := hs r hr
    have := hx r' hr'
    omega_arith

/-- The multiple of `m` the pass takes, from the rows' low words and `-m⁻¹`:
`(u a + v b) mi mod 2^64`. -/
theorem kmod {x y a0 b0 mi : BitVec 64} {u v a b : Int} (hu : x.toInt = u) (hv : y.toInt = v)
    (ha : a % 2 ^ 64 = (a0.toNat : Int)) (hb : b % 2 ^ 64 = (b0.toNat : Int)) :
    (((x * a0 + y * b0) * mi).toNat : Int) = (u * a + v * b) * mi.toNat % 2 ^ 64 := by
  have ex : u % 2 ^ 64 = (x.toNat : Int) := by
    rw [← hu, Divstep.toInt_cond]; split
    · exact Int.emod_eq_of_lt (by omega) (by have := x.isLt; omega)
    · rw [show (x.toNat : Int) - 2 ^ 64 = x.toNat + (-1) * 2 ^ 64 by omega, Int.add_mul_emod_self_right]
      exact Int.emod_eq_of_lt (by omega) (by have := x.isLt; omega)
  have ey : v % 2 ^ 64 = (y.toNat : Int) := by
    rw [← hv, Divstep.toInt_cond]; split
    · exact Int.emod_eq_of_lt (by omega) (by have := y.isLt; omega)
    · rw [show (y.toNat : Int) - 2 ^ 64 = y.toNat + (-1) * 2 ^ 64 by omega, Int.add_mul_emod_self_right]
      exact Int.emod_eq_of_lt (by omega) (by have := y.isLt; omega)
  rw [Int.mul_emod, Int.add_emod, Int.mul_emod u, Int.mul_emod v, ex, ey, ha, hb]
  simp only [BitVec.toNat_mul, BitVec.toNat_add]
  push_cast
  rw [Int.emod_eq_of_lt (a := (mi.toNat : Int)) (Int.natCast_nonneg _) (by have := mi.isLt; omega)]

/-- `s0 + 2^64 X = t + k p` with `k = t mi mod 2^64` and `p mi ≡ -1`: `s0 = 0`
and `X = mredRaw p mi t`. -/
theorem mred_words {s0 : Nat} {X t k p mi : Int} (hs0 : s0 < 2 ^ 64) (hm : (p * mi + 1) % 2 ^ 64 = 0)
    (hk : k = t * mi % 2 ^ 64) (h : (s0 : Int) + 2 ^ 64 * X = t + k * p) : X = Divstep.mredRaw p mi t := by
  have hdvd : (2 : Int) ^ 64 ∣ t + k * p := by
    have h1 : (2 : Int) ^ 64 ∣ t * (p * mi + 1) := Int.dvd_mul_of_dvd_right (Int.dvd_of_emod_eq_zero hm)
    have h2 : (2 : Int) ^ 64 ∣ t * mi - k := by rw [hk]; exact Int.dvd_self_sub_emod
    have := Int.dvd_sub h1 (Int.dvd_mul_of_dvd_left (c := p) h2)
    rw [show t * (p * mi + 1) - (t * mi - k) * p = t + k * p by grind] at this
    exact this
  obtain ⟨R, hR⟩ := hdvd
  have hK := eq_zero_of_mul_lt (r := s0) (R := 2 ^ 64) (K := R - X)
    (by rw [Int.mul_sub, ← hR, ← h]; omega) (by omega) (by exact_mod_cast hs0)
  have hmr : Divstep.mredRaw p mi t = R := by
    unfold Divstep.mredRaw; rw [← hk, hR, Int.mul_ediv_cancel_left _ (by decide)]
  rw [hmr]; omega

/-- The `a`, `b` half of a batch: `(a, b) := (mredRaw (u a + v b), mredRaw (q a + r b))`
where `-m⁻¹` is right and `a`, `b` and the results are in `(-p, 2p)`. -/
theorem abStage_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hn1 : 1 ≤ n) (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iA iB iM : Nat}
    (hA : iA < 16) (hB : iB < 16) (hM : iM < 16) (dAB : iA ≠ iB) (dAM : iA ≠ iM) (dBM : iB ≠ iM)
    {u v q r a b a' b' : Int} {p : Nat} (hp : p < 2 ^ (64 * n)) (huv : |u| + |v| ≤ 2 ^ 59) (hqr : |q| + |r| ≤ 2 ^ 59)
    (lu : s.gpr .x4 = BitVec.ofInt 64 u) (lv : s.gpr .x5 = BitVec.ofInt 64 v)
    (lq : s.gpr .x6 = BitVec.ofInt 64 q) (lr : s.gpr .x7 = BitVec.ofInt 64 r)
    (m9 : Msk s .x9 .x4) (m10 : Msk s .x10 .x5) (m19 : Msk s .x19 .x6) (m20 : Msk s .x20 .x7)
    (ea : a' = Divstep.mredRaw p (laneOf s .v18 1).toNat (u * a + v * b))
    (eb : b' = Divstep.mredRaw p (laneOf s .v18 1).toNat (q * a + r * b)) :
    WP isa (dePass iA iB iM) s fun t =>
      ((((p : Int) * (laneOf s .v18 1).toNat + 1) % 2 ^ 64 = 0 ∧ wv s.mem B (slot w iM) n = p ∧
        sgn (n + 1) (wv s.mem B (slot w iA) (n + 1)) = a ∧ sgn (n + 1) (wv s.mem B (slot w iB) (n + 1)) = b ∧
        (-(p : Int) < a ∧ a < 2 * p) ∧ (-(p : Int) < b ∧ b < 2 * p) ∧
        (-(p : Int) < a' ∧ a' < 2 * p) ∧ (-(p : Int) < b' ∧ b' < 2 * p)) →
        sgn (n + 1) (wv t.mem B (slot w iA) (n + 1)) = a' ∧ sgn (n + 1) (wv t.mem B (slot w iB) (n + 1)) = b') ∧
      Frm B [(slot w iA, 8 * (n + 1)), (slot w iB, 8 * (n + 1))] s.mem t.mem ∧
      Keep [.x1, .x2, .x3, .x8, .x13, .x14, .x16, .x17, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] s t ∧
      ∀ r l, l < 2 → r ≠ .v25 → r ≠ .v26 → laneOf t r l = laneOf s r l := by
  obtain ⟨u0, u1, v0, v1, -⟩ := Rsa.Divstep.row_parts huv
  obtain ⟨q0, q1, r0, r1, -⟩ := Rsa.Divstep.row_parts hqr
  have tu : (s.gpr .x4).toInt = u := by rw [lu]; exact Divstep.toInt_ofInt64 (by omega_arith) (by omega_arith)
  have tv : (s.gpr .x5).toInt = v := by rw [lv]; exact Divstep.toInt_ofInt64 (by omega_arith) (by omega_arith)
  have tq : (s.gpr .x6).toInt = q := by rw [lq]; exact Divstep.toInt_ofInt64 (by omega_arith) (by omega_arith)
  have tr : (s.gpr .x7).toInt = r := by rw [lr]; exact Divstep.toInt_ofInt64 (by omega_arith) (by omega_arith)
  have hL : (1 : Nat) ≤ n + 1 := by omega_arith
  refine WP.mono (dePass_ok hs h0 h11 h12 hn1 hn hw hZ hA hB hM dAB dAM dBM m9 m10 m19 m20
    (cb59_of tu tv huv) (cb59_of tq tr hqr))
    fun t ⟨⟨s0, hs0, e, he⟩, ⟨s0', hs0', e', he'⟩, fr, k, ln⟩ => ⟨fun ⟨hm, hpm, ha, hb, _, _, ra', rb'⟩ => ?_, fr, k, ln⟩
  have la : a % 2 ^ 64 = ((word s.mem B (slot w iA)).toNat : Int) := by
    rw [← ha, Divstep.sgn_mod64 hL (wv_lt _ _ _ _), wv_mod64 _ _ _ hL]
  have lb : b % 2 ^ 64 = ((word s.mem B (slot w iB)).toNat : Int) := by
    rw [← hb, Divstep.sgn_mod64 hL (wv_lt _ _ _ _), wv_mod64 _ _ _ hL]
  obtain ⟨_, ra0, ra1⟩ := Rsa.Divstep.range_parts ra' hp
  obtain ⟨_, rb0, rb1⟩ := Rsa.Divstep.range_parts rb' hp
  rw [tu, tv, ha, hb, hpm, kmod tu tv la lb] at he
  rw [tq, tr, ha, hb, hpm, kmod tq tr la lb] at he'
  refine ⟨sgn_of_cong (e := e) hL (wv_lt _ _ _ _) ra0 ra1 ?_, sgn_of_cong (e := e') hL (wv_lt _ _ _ _) rb0 rb1 ?_⟩
  · rw [ea]; exact mred_words hs0 hm rfl he
  · rw [eb]; exact mred_words hs0' hm rfl he'

end VG.Proof.Rsa.AArch64

-- From `Proof/Rsa/AArch64/InvLoop.lean`.
/-!
# RSA private keys on AArch64: the batches of divsteps

The batches of `Keys.inverseB` keep `LInv`: after `k` of them, `f`, `g`,
`a` and `b` in their arrays and `d` in lane 0 of `v18` are those of
`Divstep.invRunS 59` after `k` batches (`ICfg.st`), the modulus unchanged
and only the batches' arrays changed (`batch_ok`: `batchHead_ok`, then
`fgStage_ok` and `abStage_ok`, with `Rsa.Divstep.batch64` for what they
need). `batches_ok`: the `3 n + 2` batches.
-/


namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.InvBatch
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Divstep (sgn)

/-- The batched inverse's fixed data: the working space, the width `n`
and the arrays' stride `w`, the arrays, the modulus `p`, `-p⁻¹ mod 2^64`
and the start `x` of `g`. -/
structure ICfg where
  B : Addr
  Z : Nat
  w : Nat
  n : Nat
  iU : Nat
  iV : Nat
  iX₁ : Nat
  iX₂ : Nat
  iM : Nat
  iT : Nat
  p : Nat
  mi : BitVec 64
  x : Nat

/-- What the batches need of it. -/
structure ICfg.Ok (C : ICfg) : Prop where
  n1 : 1 ≤ C.n
  nw : C.n ≤ C.w
  w24 : C.w < 2 ^ 24
  n21 : C.n < 2 ^ 21
  hZ : slot C.w 16 ≤ C.Z
  hU : C.iU < 16
  hV : C.iV < 16
  hX₁ : C.iX₁ < 16
  hX₂ : C.iX₂ < 16
  hM : C.iM < 16
  hT : C.iT < 16
  dUV : C.iU ≠ C.iV
  dUX₁ : C.iU ≠ C.iX₁
  dUX₂ : C.iU ≠ C.iX₂
  dUM : C.iU ≠ C.iM
  dUT : C.iU ≠ C.iT
  dVX₁ : C.iV ≠ C.iX₁
  dVX₂ : C.iV ≠ C.iX₂
  dVM : C.iV ≠ C.iM
  dVT : C.iV ≠ C.iT
  dX : C.iX₁ ≠ C.iX₂
  dX₁M : C.iX₁ ≠ C.iM
  dX₁T : C.iX₁ ≠ C.iT
  dX₂M : C.iX₂ ≠ C.iM
  dX₂T : C.iX₂ ≠ C.iT
  dMT : C.iM ≠ C.iT
  pC : C.p < 2 ^ (64 * C.n)
  xC : C.x < 2 ^ (64 * C.n + 1)
  hm : ((C.p + (1 - C.p % 2) : Nat) * C.mi.toNat + 1 : Int) % 2 ^ 64 = 0

/-- The odd start of `f`: `p`, or `p + 1` for an even `p`. -/
def ICfg.pf (C : ICfg) : Nat := C.p + (1 - C.p % 2)

/-- The modulus the inverse is right for: odd and above 1. -/
def ICfg.Good (C : ICfg) : Prop := C.p % 2 = 1 ∧ 1 < C.p

/-- The state after `k` batches. -/
def ICfg.st (C : ICfg) (k : Nat) : Divstep.IState := Divstep.invRunS 59 C.pf C.mi.toNat C.x k

/-- The arrays the batches change. -/
def ICfg.ranges (C : ICfg) : List (Nat × Nat) :=
  [(slot C.w C.iU, 8 * (C.w + 2)), (slot C.w C.iV, 8 * (C.w + 2)), (slot C.w C.iX₁, 8 * (C.w + 2)),
    (slot C.w C.iX₂, 8 * (C.w + 2)), (slot C.w C.iT, 8 * (C.w + 2))]

/-- The state between batches, after `k` of them from `s₀`. -/
structure LInv (C : ICfg) (s₀ : State) (k : Nat) (s : State) : Prop where
  scr : Scr s C.B C.Z
  x0 : s.gpr .x0 = C.B
  x11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (C.w + 2))
  x12 : s.gpr .x12 = BitVec.ofNat 64 C.n
  f : sgn (C.n + 1) (wv s.mem C.B (slot C.w C.iV) (C.n + 1)) = (C.st k).f
  g : sgn (C.n + 1) (wv s.mem C.B (slot C.w C.iU) (C.n + 1)) = (C.st k).g
  a : C.Good → sgn (C.n + 1) (wv s.mem C.B (slot C.w C.iX₂) (C.n + 1)) = (C.st k).a
  b : C.Good → sgn (C.n + 1) (wv s.mem C.B (slot C.w C.iX₁) (C.n + 1)) = (C.st k).b
  d : laneOf s .v18 0 = BitVec.ofInt 64 (C.st k).d
  mi : laneOf s .v18 1 = C.mi
  m : wv s.mem C.B (slot C.w C.iM) C.n = C.p
  frm : Frm C.B C.ranges s₀.mem s.mem
  keep : Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s₀ s
  x1s : laneOf s .v19 0 = s₀.gpr .x1
  x2s : laneOf s .v19 1 = s₀.gpr .x2

/-- Array `j` is apart from three others' parts. -/
theorem apart3 {w j a b c L la lb lc : Nat} (hja : j ≠ a) (hjb : j ≠ b) (hjc : j ≠ c) (hL : L ≤ w + 2)
    (ha : la ≤ 8 * (w + 2)) (hb : lb ≤ 8 * (w + 2)) (hc : lc ≤ 8 * (w + 2)) :
    ∀ r ∈ [(slot w a, la), (slot w b, lb), (slot w c, lc)], slot w j + 8 * L ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact slot_apart (w := w) hja (by omega_arith) ha
  · exact slot_apart (w := w) hjb (by omega_arith) hb
  · exact slot_apart (w := w) hjc (by omega_arith) hc

/-- `x19`–`x28` and their lanes. -/
def hiKs : List (Reg × VReg × Nat) :=
  [(.x19, .v20, 0), (.x20, .v20, 1), (.x21, .v21, 0), (.x22, .v21, 1), (.x23, .v22, 0), (.x24, .v22, 1),
    (.x25, .v23, 0), (.x26, .v23, 1), (.x27, .v24, 0), (.x28, .v24, 1)]

theorem saveHi_eq : saveHi = insOf hiKs := rfl

/-- The lanes `hiKs` leaves alone. -/
theorem hiKs_other (v : VReg) (l : Nat) (hl : l < 2) (hv : v ∉ [VReg.v20, .v21, .v22, .v23, .v24]) :
    (v, l) ∉ hiKs.map (fun k => (k.2.1, k.2.2)) := by
  rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl <;> cases v <;> simp_all [hiKs]
theorem restoreHi_eq : restoreHi = umovOf hiKs := rfl

/-- `hiKs`' lanes are below 2 and none of the batch's own. -/
theorem hiKs_lane : ∀ k ∈ hiKs, k.2.2 < 2 ∧ k.2.1 ≠ .v16 ∧ k.2.1 ≠ .v17 ∧ k.2.1 ≠ .v18 ∧ k.2.1 ≠ .v25 ∧
    k.2.1 ≠ .v26 := by decide

/-- The callee-saved vectors are none of the batch's. -/
theorem pres_lane : ∀ r ∈ preservedV, r ≠ .v16 ∧ r ≠ .v17 ∧ r ≠ .v18 ∧ r ≠ .v25 ∧ r ≠ .v26 ∧
    r ∉ [VReg.v20, .v21, .v22, .v23, .v24] := by decide

/-- The registers a batch writes but `x19`–`x28`, which it restores. -/
theorem batch_regs : ∀ r : Reg, r ∉ [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15,
    .x16, .x17] → r ∉ hiKs.map Prod.fst → r ∉ [] ++ (([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11,
    .x12, .x13, .x14, .x15, .x16, .x17] : List Reg) ++ ([.x4, .x5, .x6, .x7, .x9, .x10, .x13, .x19, .x20] : List Reg)) ++
    (([.x1, .x2, .x3, .x13, .x14, .x16, .x17, .x21, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg) ++
    ([.x1, .x2, .x3, .x8, .x13, .x14, .x16, .x17, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] : List Reg)) := by
  intro r; cases r <;> decide

/-- The matrix from its lanes into `x4`–`x7`, and its sign masks. -/
theorem coefMasks4_ok (s : State) :
    WP isa (.block coefMasks4) s fun t =>
      (t.gpr .x4 = laneOf s .v16 0 ∧ t.gpr .x5 = laneOf s .v16 1 ∧ t.gpr .x6 = laneOf s .v17 0 ∧
        t.gpr .x7 = laneOf s .v17 1 ∧ Msk t .x9 .x4 ∧ Msk t .x10 .x5 ∧ Msk t .x19 .x6 ∧ Msk t .x20 .x7 ∧
        t.mem = s.mem ∧ t.v = s.v) ∧ Keep [.x4, .x5, .x6, .x7, .x9, .x10, .x13, .x19, .x20] s t := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  unfold coefMasks4 Msk
  brun [exec_umov (show 0 < 2 by decide), exec_umov (show 1 < 2 by decide),
    show BitVec.setWidth 64 0#16 = 0#64 from rfl]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `hiKs`' registers are none of `x1`–`x17`. -/
theorem hiKs_regs : ∀ k ∈ hiKs, k.1 ∉ [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14,
    .x15, .x16, .x17] := by decide

/-- The registers the front of a batch writes but `x19`–`x28`. -/
theorem batch_regs_front : ∀ r : Reg, r ∉ [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14,
    .x15, .x16, .x17] → r ∉ hiKs.map Prod.fst → r ∉ (([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11,
    .x12, .x13, .x14, .x15, .x16, .x17] : List Reg) ++ ([.x4, .x5, .x6, .x7, .x9, .x10, .x13, .x19, .x20] : List Reg)) ++
    ([.x1, .x2, .x3, .x13, .x14, .x16, .x17, .x21, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg) := by
  intro r; cases r <;> decide

/-- The registers the back of a batch writes but `x19`–`x28`. -/
theorem batch_regs_back : ∀ r : Reg, r ∉ [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14,
    .x15, .x16, .x17] → r ∉ hiKs.map Prod.fst →
    r ∉ [.x1, .x2, .x3, .x8, .x13, .x14, .x16, .x17, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] := by
  intro r; cases r <;> decide

/-- For a good `p`: `pf = p`, and the `a`, `b` the back of a batch writes are
those of the next batch. -/
theorem batch_ab {C : ICfg} (hC : C.Ok) {s₀ s s₄ t : State} {k : Nat} (hI : LInv C s₀ k s)
    (hpm : wv s₄.mem C.B (slot C.w C.iM) C.n = C.p)
    (hA : wv s₄.mem C.B (slot C.w C.iX₂) (C.n + 1) = wv s.mem C.B (slot C.w C.iX₂) (C.n + 1))
    (hB : wv s₄.mem C.B (slot C.w C.iX₁) (C.n + 1) = wv s.mem C.B (slot C.w C.iX₁) (C.n + 1)) {A' B' : Int}
    (abv : (((C.p : Int) * C.mi.toNat + 1) % 2 ^ 64 = 0 ∧ wv s₄.mem C.B (slot C.w C.iM) C.n = C.p ∧
        sgn (C.n + 1) (wv s₄.mem C.B (slot C.w C.iX₂) (C.n + 1)) = (C.st k).a ∧
        sgn (C.n + 1) (wv s₄.mem C.B (slot C.w C.iX₁) (C.n + 1)) = (C.st k).b ∧
        (-(C.p : Int) < (C.st k).a ∧ (C.st k).a < 2 * C.p) ∧ (-(C.p : Int) < (C.st k).b ∧ (C.st k).b < 2 * C.p) ∧
        (-(C.p : Int) < A' ∧ A' < 2 * C.p) ∧ (-(C.p : Int) < B' ∧ B' < 2 * C.p)) →
      sgn (C.n + 1) (wv t.mem C.B (slot C.w C.iX₂) (C.n + 1)) = A' ∧
        sgn (C.n + 1) (wv t.mem C.B (slot C.w C.iX₁) (C.n + 1)) = B')
    (eA : A' = Divstep.mredRaw C.p C.mi.toNat
      ((Divstep.msteps 59 (Divstep.MSt.init (C.st k).d (C.st k).f (C.st k).g)).u * (C.st k).a +
        (Divstep.msteps 59 (Divstep.MSt.init (C.st k).d (C.st k).f (C.st k).g)).v * (C.st k).b))
    (eB : B' = Divstep.mredRaw C.p C.mi.toNat
      ((Divstep.msteps 59 (Divstep.MSt.init (C.st k).d (C.st k).f (C.st k).g)).q * (C.st k).a +
        (Divstep.msteps 59 (Divstep.MSt.init (C.st k).d (C.st k).f (C.st k).g)).r * (C.st k).b)) :
    (C.Good → sgn (C.n + 1) (wv t.mem C.B (slot C.w C.iX₂) (C.n + 1)) = (C.st (k + 1)).a) ∧
      (C.Good → sgn (C.n + 1) (wv t.mem C.B (slot C.w C.iX₁) (C.n + 1)) = (C.st (k + 1)).b) := by
  suffices h : C.Good → sgn (C.n + 1) (wv t.mem C.B (slot C.w C.iX₂) (C.n + 1)) = (C.st (k + 1)).a ∧
      sgn (C.n + 1) (wv t.mem C.B (slot C.w C.iX₁) (C.n + 1)) = (C.st (k + 1)).b from
    ⟨fun G => (h G).1, fun G => (h G).2⟩
  intro G
  have hpf : C.pf = C.p := by unfold ICfg.pf; have := G.1; omega_arith
  have hm' : ((C.p : Int) * C.mi.toNat + 1) % 2 ^ 64 = 0 := by
    have := hC.hm; rw [show C.p + (1 - C.p % 2) = C.p by have := G.1; omega_arith] at this; exact this
  have hp1 : (1 : Int) < C.p := by exact_mod_cast G.2
  obtain ⟨⟨a0, a1, b0, b1⟩, ea, eb⟩ := Rsa.Divstep.batch64ab (k := k) (x := (C.x : Int)) hp1 hm'
  obtain ⟨ra0, ra1, rb0, rb1⟩ := Divstep.invRunS_range (N := 59) (p := C.p) (m := C.mi.toNat) (x := C.x)
    (by decide) hp1 hm' (k + 1)
  have ha := hI.a G
  have hb := hI.b G
  rw [← hA] at ha; rw [← hB] at hb
  have sk : C.st k = Divstep.invRunS 59 C.p C.mi.toNat C.x k := by simp only [ICfg.st]; rw [hpf]
  have sk1 : C.st (k + 1) = Divstep.invRunS 59 C.p C.mi.toNat C.x (k + 1) := by simp only [ICfg.st]; rw [hpf]
  rw [sk] at eA eB
  have e1 : (C.st (k + 1)).a = A' := by rw [sk1, ea, eA]
  have e2 : (C.st (k + 1)).b = B' := by rw [sk1, eb, eB]
  rw [sk1] at e1 e2
  rw [e1] at ra0 ra1; rw [e2] at rb0 rb1
  obtain ⟨r1, r2⟩ := abv ⟨hm', hpm, ha, hb, by rw [sk]; exact ⟨a0, a1⟩, by rw [sk]; exact ⟨b0, b1⟩, ⟨ra0, ra1⟩, ⟨rb0, rb1⟩⟩
  rw [sk1, e1, e2]
  exact ⟨r1, r2⟩

/-- `x19`–`x28` back from their lanes after the back of a batch, the rest kept. -/
theorem keep_hi {s₀ s₄ s₅ t : State}
    (k₅ : Keep [.x1, .x2, .x3, .x8, .x13, .x14, .x16, .x17, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] s₄ s₅)
    (rest : ∀ k ∈ hiKs, t.gpr k.1 = laneOf s₅ k.2.1 k.2.2) (oth : ∀ r, r ∉ hiKs.map Prod.fst → t.gpr r = s₅.gpr r)
    (rdt : t.rd = s₅.rd) (wrt : t.wr = s₅.wr) (spt : t.sp = s₅.sp) (vt : t.v = s₅.v)
    (ln₅ : ∀ r l, l < 2 → r ≠ .v25 → r ≠ .v26 → laneOf s₅ r l = laneOf s₄ r l)
    (hi₄ : ∀ k ∈ hiKs, laneOf s₄ k.2.1 k.2.2 = s₀.gpr k.1)
    (keep₄ : ∀ r : Reg, r ∉ [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15,
      .x16, .x17] → r ∉ hiKs.map Prod.fst → s₄.gpr r = s₀.gpr r)
    (rd₄ : s₄.rd = s₀.rd) (wr₄ : s₄.wr = s₀.wr) (sp₄ : s₄.sp = s₀.sp)
    (vcs₄ : ∀ r ∈ preservedV, (s₄.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64) :
    Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s₀ t := by
  have lnT : ∀ v l, l < 2 → v ≠ .v25 → v ≠ .v26 → laneOf t v l = laneOf s₄ v l := fun v l hl d e => by
    rw [show laneOf t v l = laneOf s₅ v l by unfold laneOf; rw [vt], ln₅ v l hl d e]
  refine ⟨fun r hr => ?_, rdt.trans (k₅.rd.trans rd₄), wrt.trans (k₅.wr.trans wr₄),
    spt.trans (k₅.sp.trans sp₄), fun r hr => ?_⟩
  · by_cases hh : r ∈ hiKs.map Prod.fst
    · obtain ⟨⟨r', v, l⟩, hk, rfl⟩ := List.mem_map.mp hh
      obtain ⟨hl, -, -, -, h25, h26⟩ := hiKs_lane _ hk
      rw [rest _ hk, show laneOf s₅ v l = laneOf t v l by unfold laneOf; rw [vt], lnT v l hl h25 h26]
      exact hi₄ _ hk
    · rw [oth r hh, k₅.gpr r (batch_regs_back r hr hh)]
      exact keep₄ r hr hh
  · obtain ⟨-, -, -, p25, p26, -⟩ := pres_lane r hr
    rw [show (t.v r).extractLsb' 0 64 = laneOf t r 0 from rfl, lnT r 0 (by decide) p25 p26]
    exact vcs₄ r hr

/-- The back of a batch: `(a, b)` and `x19`–`x28` back from their lanes, from
what its front leaves. -/
theorem batchDE_ok {C : ICfg} (hC : C.Ok) {s₀ s s₄ : State} {k : Nat} (hI : LInv C s₀ k s)
    (hs₄ : Scr s₄ C.B C.Z) (x0₄ : s₄.gpr .x0 = C.B) (x11₄ : s₄.gpr .x11 = BitVec.ofNat 64 (8 * (C.w + 2)))
    (x12₄ : s₄.gpr .x12 = BitVec.ofNat 64 C.n) (x15₄ : s₄.gpr .x15 = s.gpr .x15 - 1#64)
    (lu : s₄.gpr .x4 = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init (C.st k).d (C.st k).f (C.st k).g)).u)
    (lv : s₄.gpr .x5 = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init (C.st k).d (C.st k).f (C.st k).g)).v)
    (lq : s₄.gpr .x6 = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init (C.st k).d (C.st k).f (C.st k).g)).q)
    (lr : s₄.gpr .x7 = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init (C.st k).d (C.st k).f (C.st k).g)).r)
    (m9 : Msk s₄ .x9 .x4) (m10 : Msk s₄ .x10 .x5) (m19 : Msk s₄ .x19 .x6) (m20 : Msk s₄ .x20 .x7)
    (f₄ : sgn (C.n + 1) (wv s₄.mem C.B (slot C.w C.iV) (C.n + 1)) = (C.st (k + 1)).f)
    (g₄ : sgn (C.n + 1) (wv s₄.mem C.B (slot C.w C.iU) (C.n + 1)) = (C.st (k + 1)).g)
    (keepFG : ∀ {j L : Nat}, j ≠ C.iV → j ≠ C.iU → L ≤ C.w + 2 → j < 16 →
      wv s₄.mem C.B (slot C.w j) L = wv s.mem C.B (slot C.w j) L)
    (frm₄ : Frm C.B C.ranges s₀.mem s₄.mem)
    (d₄ : laneOf s₄ .v18 0 = BitVec.ofInt 64 (C.st (k + 1)).d) (mi₄ : laneOf s₄ .v18 1 = C.mi)
    (x1s₄ : laneOf s₄ .v19 0 = s₀.gpr .x1) (x2s₄ : laneOf s₄ .v19 1 = s₀.gpr .x2)
    (hi₄ : ∀ k ∈ hiKs, laneOf s₄ k.2.1 k.2.2 = s₀.gpr k.1)
    (keep₄ : ∀ r : Reg, r ∉ [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15,
      .x16, .x17] → r ∉ hiKs.map Prod.fst → s₄.gpr r = s₀.gpr r)
    (rd₄ : s₄.rd = s₀.rd) (wr₄ : s₄.wr = s₀.wr) (sp₄ : s₄.sp = s₀.sp)
    (vcs₄ : ∀ r ∈ preservedV, (s₄.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64)
    (buv : |(Divstep.msteps 59 (Divstep.MSt.init (C.st k).d (C.st k).f (C.st k).g)).u| +
      |(Divstep.msteps 59 (Divstep.MSt.init (C.st k).d (C.st k).f (C.st k).g)).v| ≤ 2 ^ 59)
    (bqr : |(Divstep.msteps 59 (Divstep.MSt.init (C.st k).d (C.st k).f (C.st k).g)).q| +
      |(Divstep.msteps 59 (Divstep.MSt.init (C.st k).d (C.st k).f (C.st k).g)).r| ≤ 2 ^ 59) :
    WP isa (.seq (dePass C.iX₂ C.iX₁ C.iM) (.block restoreHi)) s₄ fun t =>
      LInv C s₀ (k + 1) t ∧ t.gpr .x15 = s.gpr .x15 - 1#64 := by
  have hnL : C.n + 1 ≤ C.w + 2 := by have := hC.nw; omega
  have hnL' : C.n ≤ C.w + 2 := by have := hC.nw; omega
  have hn8 : 8 * (C.n + 1) ≤ 8 * (C.w + 2) := by omega
  have sl : ∀ {j : Nat}, j < 16 → slot C.w j + 8 * (C.w + 2) ≤ 2 ^ 64 := fun hj => by
    have := slot_lt (w := C.w) hj; have := hI.scr.nowrap; have := hC.hZ; omega
  have apart2 : ∀ {j a b L : Nat}, j ≠ a → j ≠ b → L ≤ C.w + 2 →
      ∀ r ∈ [(slot C.w a, 8 * (C.n + 1)), (slot C.w b, 8 * (C.n + 1))], slot C.w j + 8 * L ≤ r.1 ∨ r.1 + r.2 ≤ slot C.w j :=
    fun {j a b L} ha hb hL' r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slot_apart (w := C.w) ha (by omega) hn8
      · exact slot_apart (w := C.w) hb (by omega) hn8
  have wid : ∀ {j : Nat} {L : Nat}, (slot C.w j, 8 * (C.w + 2)) ∈ C.ranges → L ≤ 8 * (C.w + 2) →
      ∃ r' ∈ C.ranges, r'.1 ≤ slot C.w j ∧ slot C.w j + L ≤ r'.1 + r'.2 := fun {j L} h hL' =>
    ⟨_, h, Nat.le_refl _, Nat.add_le_add_left hL' _⟩
  refine WP.seq (WP.mono (abStage_ok hs₄ x0₄ x11₄ x12₄ hC.n1 hC.nw hC.w24 hC.hZ hC.hX₂ hC.hX₁ hC.hM
    hC.dX.symm hC.dX₂M hC.dX₁M hC.pC buv bqr lu lv lq lr m9 m10 m19 m20 (a := (C.st k).a) (b := (C.st k).b) rfl rfl)
    fun s₅ ⟨abv, fr₅, k₅, ln₅⟩ => ?_)
  refine WP.mono (WP.vfix (show WP isa (.block (umovOf hiKs)) s₅ _ from umovOf_ok hiKs s₅ (by decide) (by decide))
    (by decide)) fun t ⟨⟨mt, rdt, wrt, spt, rest, oth⟩, vt⟩ => ?_
  have keepAB : ∀ {j L : Nat}, j ≠ C.iX₂ → j ≠ C.iX₁ → L ≤ C.w + 2 → j < 16 →
      wv t.mem C.B (slot C.w j) L = wv s₄.mem C.B (slot C.w j) L := fun {j L} a b hL' hj => by
    rw [mt]; exact fr₅.wv_eq (apart2 a b hL') (Nat.le_trans (Nat.add_le_add_left (by omega) _) (sl hj))
  have lnT : ∀ v l, l < 2 → v ≠ .v25 → v ≠ .v26 → laneOf t v l = laneOf s₄ v l := fun v l hl d e => by
    rw [show laneOf t v l = laneOf s₅ v l by unfold laneOf; rw [vt], ln₅ v l hl d e]
  have hpm : wv s₄.mem C.B (slot C.w C.iM) C.n = C.p := by
    rw [keepFG hC.dVM.symm hC.dUM.symm hnL' hC.hM]; exact hI.m
  have ab₃ := batch_ab hC hI hpm (by rw [keepFG hC.dVX₂.symm hC.dUX₂.symm hnL hC.hX₂])
    (by rw [keepFG hC.dVX₁.symm hC.dUX₁.symm hnL hC.hX₁]) (by rw [mi₄] at abv; exact abv) rfl rfl
  have kk := keep_hi k₅ rest oth rdt wrt spt vt ln₅ hi₄ keep₄ rd₄ wr₄ sp₄ vcs₄
  have F1 : sgn (C.n + 1) (wv t.mem C.B (slot C.w C.iV) (C.n + 1)) = (C.st (k + 1)).f := by
    rw [keepAB hC.dVX₂ hC.dVX₁ hnL hC.hV]; exact f₄
  have F2 : sgn (C.n + 1) (wv t.mem C.B (slot C.w C.iU) (C.n + 1)) = (C.st (k + 1)).g := by
    rw [keepAB hC.dUX₂ hC.dUX₁ hnL hC.hU]; exact g₄
  have D : laneOf t .v18 0 = BitVec.ofInt 64 (C.st (k + 1)).d := by
    rw [lnT _ _ (by decide) (by decide) (by decide)]; exact d₄
  have MI : laneOf t .v18 1 = C.mi := by rw [lnT _ _ (by decide) (by decide) (by decide)]; exact mi₄
  have MM : wv t.mem C.B (slot C.w C.iM) C.n = C.p := by
    rw [keepAB hC.dX₂M.symm hC.dX₁M.symm hnL' hC.hM, keepFG hC.dVM.symm hC.dUM.symm hnL' hC.hM]; exact hI.m
  have FR : Frm C.B C.ranges s₀.mem t.mem := by
    rw [mt]
    refine frm₄.trans (Frm.widen fr₅ ?_)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> refine wid (by simp [ICfg.ranges]) hn8
  have X1 : laneOf t .v19 0 = s₀.gpr .x1 := by rw [lnT _ _ (by decide) (by decide) (by decide)]; exact x1s₄
  have X2 : laneOf t .v19 1 = s₀.gpr .x2 := by rw [lnT _ _ (by decide) (by decide) (by decide)]; exact x2s₄
  have R0 : t.gpr .x0 = C.B := (oth _ (by decide)).trans ((k₅.gpr .x0 (by decide)).trans x0₄)
  have R11 : t.gpr .x11 = BitVec.ofNat 64 (8 * (C.w + 2)) := (oth _ (by decide)).trans ((k₅.gpr .x11 (by decide)).trans x11₄)
  have R12 : t.gpr .x12 = BitVec.ofNat 64 C.n := (oth _ (by decide)).trans ((k₅.gpr .x12 (by decide)).trans x12₄)
  have R15 : t.gpr .x15 = s.gpr .x15 - 1#64 := (oth _ (by decide)).trans ((k₅.gpr .x15 (by decide)).trans x15₄)
  have SC : Scr t C.B C.Z := hs₄.congr (wrt.trans k₅.wr)
  have AB1 : C.Good → sgn (C.n + 1) (wv t.mem C.B (slot C.w C.iX₂) (C.n + 1)) = (C.st (k + 1)).a := by
    rw [mt]; exact ab₃.1
  have AB2 : C.Good → sgn (C.n + 1) (wv t.mem C.B (slot C.w C.iX₁) (C.n + 1)) = (C.st (k + 1)).b := by
    rw [mt]; exact ab₃.2
  exact ⟨LInv.mk SC R0 R11 R12 F1 F2 AB1 AB2 D MI MM FR kk X1 X2, R15⟩

/-- A batch keeps `LInv`, one batch on. -/
theorem batch_ok {C : ICfg} (hC : C.Ok) {s₀ s : State} {k : Nat} (hk : k < 3 * C.n + 2) (hI : LInv C s₀ k s) :
    WP isa (batch C.iV C.iU C.iX₂ C.iX₁ C.iM) s fun t =>
      LInv C s₀ (k + 1) t ∧ t.gpr .x15 = s.gpr .x15 - 1#64 := by
  have hn' := hI.scr.nowrap
  have hnL : C.n + 1 ≤ C.w + 2 := by have := hC.nw; omega
  have hn8 : 8 * (C.n + 1) ≤ 8 * (C.w + 2) := by omega
  have sl : ∀ {j : Nat}, j < 16 → slot C.w j + 8 * (C.w + 2) ≤ 2 ^ 64 := fun hj => by
    have := slot_lt (w := C.w) hj; have := hC.hZ; omega
  have hpC : (C.pf : Int) < 2 ^ (64 * C.n + 1) := by
    have := hC.pC; have : C.pf < 2 ^ (64 * C.n + 1) := by
      unfold ICfg.pf; rw [Nat.pow_succ]; omega_arith
    exact_mod_cast this
  have hxC : (C.x : Int) < 2 ^ (64 * C.n + 1) := by exact_mod_cast hC.xC
  obtain ⟨fodd, dbnd, bf, bg, buv, bqr, ef, eg, ed⟩ :=
    Rsa.Divstep.batch64fg (n := C.n) (k := k) (p := C.pf) (m := C.mi.toNat) (x := C.x)
      (by unfold ICfg.pf; omega_arith) (by omega_arith) (by omega_arith) hpC hxC (by have := hC.n21; omega_arith)
  have hL : (1 : Nat) ≤ C.n + 1 := by omega
  -- The low words of `f` and `g`.
  have low : ∀ {j : Nat} {y : Int}, sgn (C.n + 1) (wv s.mem C.B (slot C.w j) (C.n + 1)) = y →
      ((word s.mem C.B (slot C.w j)).toNat : Int) % 2 ^ 64 = y % 2 ^ 64 := fun {j y} h => by
    rw [← h, Divstep.sgn_mod64 hL (wv_lt _ _ _ _), wv_mod64 _ _ _ hL]
    exact Int.emod_eq_of_lt (by omega) (by have := (word s.mem C.B (slot C.w j)).isLt; omega)
  have apartFG : ∀ {j L : Nat}, j ≠ C.iV → j ≠ C.iU → L ≤ C.w + 2 →
      ∀ r ∈ [(slot C.w C.iV, 8 * (C.n + 1)), (slot C.w C.iU, 8 * (C.n + 1))],
        slot C.w j + 8 * L ≤ r.1 ∨ r.1 + r.2 ≤ slot C.w j :=
    fun {j L} ha hb hL' r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slot_apart (w := C.w) ha (by omega) hn8
      · exact slot_apart (w := C.w) hb (by omega) hn8
  have wid : ∀ {j : Nat} {L : Nat}, (slot C.w j, 8 * (C.w + 2)) ∈ C.ranges → L ≤ 8 * (C.w + 2) →
      ∃ r' ∈ C.ranges, r'.1 ≤ slot C.w j ∧ slot C.w j + L ≤ r'.1 + r'.2 := fun {j L} h hL' =>
    ⟨_, h, Nat.le_refl _, Nat.add_le_add_left hL' _⟩
  unfold batch
  simp only [seqs]
  -- `x19`–`x28` into their lanes.
  refine WP.seq (WP.mono (WP.keep [] (show WP isa (.block (insOf hiKs)) s _ from
    insOf_ok hiKs s (by decide) (by decide)) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨g₁, m₁, _, _, _, l₁, o₁⟩, k₁⟩ => ?_)
  have e₁ : ∀ r, s₁.gpr r = s.gpr r := fun r => by rw [g₁]
  have lo₁ : ∀ v l, l < 2 → v ∉ [VReg.v20, .v21, .v22, .v23, .v24] → laneOf s₁ v l = laneOf s v l :=
    fun v l hl hv => o₁ v l hl (hiKs_other v l hl hv)
  have I1 : Scr s₁ C.B C.Z := hI.scr.congr k₁.wr
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (batchHead_ok I1 ((e₁ _).trans hI.x0) ((e₁ _).trans hI.x11)
    ((e₁ _).trans hI.x12) hC.nw hC.w24 hC.hZ hC.hV hC.hU (d := (C.st k).d) (f := (C.st k).f) (g := (C.st k).g)
    dbnd fodd
    (by rw [lo₁ _ _ (by decide) (by decide)]; exact hI.d) (by rw [m₁]; exact low hI.f) (by rw [m₁]; exact low hI.g))
    fun s₂ ⟨l1, l2, l3, l4, l5, l6, lv, h11, h12, h15, hm₂, k₂⟩ =>
      WP.mono (coefMasks4_ok s₂) fun s₃ ⟨⟨c4, c5, c6, c7, n9, n10, n19, n20, hm₃, v₃⟩, k₃⟩ => ?_))
  have mem₃ : s₃.mem = s.mem := hm₃.trans (hm₂.trans m₁)
  have k13 := k₂.trans k₃
  have x0₃ : s₃.gpr .x0 = C.B := (k13.gpr .x0 (by decide)).trans ((e₁ _).trans hI.x0)
  have x11₃ : s₃.gpr .x11 = BitVec.ofNat 64 (8 * (C.w + 2)) := (k₃.gpr .x11 (by decide)).trans (h11.trans ((e₁ _).trans hI.x11))
  have x12₃ : s₃.gpr .x12 = BitVec.ofNat 64 C.n := (k₃.gpr .x12 (by decide)).trans (h12.trans ((e₁ _).trans hI.x12))
  refine WP.seq (WP.mono (fgStage_ok (hI.scr.congr ((k₁.trans k13).wr)) x0₃ x11₃ x12₃ hC.n1 hC.nw hC.w24 hC.hZ
    hC.hV hC.hU hC.dUV.symm buv bqr (c4.trans l3) (c5.trans l4) (c6.trans l5) (c7.trans l6) n9 n10 n19 n20
    (by rw [mem₃]; exact hI.f) (by rw [mem₃]; exact hI.g) bf bg ef eg) fun s₄ ⟨f₄, g₄, fr₄, k₄, v₄⟩ => ?_)
  have q4 : ∀ r : Reg, r ∈ [.x0, .x4, .x5, .x6, .x7, .x9, .x10, .x11, .x12, .x15, .x19, .x20] → s₄.gpr r = s₃.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact k₄.gpr _ (by decide)
  have M : ∀ {m c : Reg}, m ∈ [.x9, .x10, .x19, .x20] → c ∈ [.x4, .x5, .x6, .x7] → Msk s₃ m c → Msk s₄ m c :=
    fun {m c} hm hc h => by
      unfold Msk at h ⊢
      rw [q4 m (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; rcases hm with rfl | rfl | rfl | rfl <;> simp),
        q4 c (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢; rcases hc with rfl | rfl | rfl | rfl <;> simp), h]
  have l4s : ∀ v l, v ≠ .v16 → v ≠ .v17 → v ≠ .v18 → laneOf s₄ v l = laneOf s₁ v l := fun v l a b c => by
    unfold laneOf; rw [v₄, v₃, lv v a b c]
  have K := (k₁.trans k13).trans k₄
  exact batchDE_ok hC hI (hI.scr.congr K.wr) ((q4 _ (by decide)).trans x0₃) ((q4 _ (by decide)).trans x11₃)
    ((q4 _ (by decide)).trans x12₃)
    (by rw [q4 _ (by decide), k₃.gpr .x15 (by decide), h15, e₁])
    ((q4 _ (by decide)).trans (c4.trans l3)) ((q4 _ (by decide)).trans (c5.trans l4))
    ((q4 _ (by decide)).trans (c6.trans l5)) ((q4 _ (by decide)).trans (c7.trans l6))
    (M (by decide) (by decide) n9) (M (by decide) (by decide) n10) (M (by decide) (by decide) n19)
    (M (by decide) (by decide) n20) f₄ g₄
    (fun {j L} a b hL' hj => by
      rw [fr₄.wv_eq (apartFG a b hL') (Nat.le_trans (Nat.add_le_add_left (by omega) _) (sl hj)), mem₃])
    ((hI.frm.trans (by rw [mem₃]; exact Frm.refl _ _ _)).trans (Frm.widen fr₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact wid (by simp [ICfg.ranges]) hn8)))
    (by rw [show laneOf s₄ .v18 0 = laneOf s₂ .v18 0 by unfold laneOf; rw [v₄, v₃], l1]; exact congrArg _ ed.symm)
    (by rw [show laneOf s₄ .v18 1 = laneOf s₂ .v18 1 by unfold laneOf; rw [v₄, v₃], l2,
      lo₁ _ _ (by decide) (by decide), hI.mi])
    (by rw [l4s _ _ (by decide) (by decide) (by decide), lo₁ _ _ (by decide) (by decide)]; exact hI.x1s)
    (by rw [l4s _ _ (by decide) (by decide) (by decide), lo₁ _ _ (by decide) (by decide)]; exact hI.x2s)
    (fun k hk => by
      obtain ⟨-, h16, h17, h18, -, -⟩ := hiKs_lane _ hk
      rw [l4s _ _ h16 h17 h18, l₁ _ hk]; exact hI.keep.gpr _ (hiKs_regs _ hk))
    (fun r hr hh => (K.gpr r (by simpa using batch_regs_front r hr hh)).trans (hI.keep.gpr r hr))
    (K.rd.trans hI.keep.rd) (K.wr.trans hI.keep.wr) (K.sp.trans hI.keep.sp)
    (fun r hr => by
      obtain ⟨p16, p17, p18, -, -, phi⟩ := pres_lane r hr
      rw [show (s₄.v r).extractLsb' 0 64 = laneOf s₄ r 0 from rfl, l4s r 0 p16 p17 p18,
        lo₁ _ _ (by decide) phi]
      exact hI.keep.vcs r hr) buv bqr

/-- The `3 n + 2` batches, counted by `x15`. -/
theorem batches_ok {C : ICfg} (hC : C.Ok) {s₀ s : State} (hI : LInv C s₀ 0 s)
    (h15 : s.gpr .x15 = BitVec.ofNat 64 (3 * C.n + 2)) :
    WP isa (.loop (batch C.iV C.iU C.iX₂ C.iX₁ C.iM) (.nonzero .x .x15)) s (LInv C s₀ (3 * C.n + 2)) :=
  wp_countdown (N := 3 * C.n + 2) (by have := hC.n21; omega_arith) (by omega_arith) (LInv C s₀)
    (fun _ hj _ hI' _ => batch_ok hC hj hI') hI h15

end VG.Proof.Rsa.AArch64

-- From `Proof/Rsa/AArch64/InvPieces.lean`.
/-!
# RSA private keys on AArch64: pieces of the batched inverse's start and end

The masked addition in place (`addMIP_ok`, `addMBody`'s loop with its output
the addend), the address of word `n` of an array (`topAt_ok`) and its
clearing (`zeroTop_ok`) and sign (`signMask_ok`), and the blocks of
`Keys.batchInit` (`initHead_ok`, `initLast_ok`).
-/


namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.InvBatch
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- A step of `addMBody`'s loop, `[x5]` possibly `[x8]`. -/
theorem maStepIP_ok {s₀ : State} {B : Addr} {Z w eo eN eA : Nat} {c : Bool} (h15 : s₀.gpr .x15 = mask c)
    (ho : eo + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z) (hA : eA + 8 * w ≤ Z)
    (sN : eN + 8 * w ≤ eo ∨ eo + 8 * w ≤ eN) (sA : eo ≤ eA ∨ eA + 8 * w ≤ eo)
    {j : Nat} (hj : j < w) {t : State} (hI : MaInv s₀ B Z eo eN eA c j t) :
    WP isa (.block ([ld .x3 .x10, .logic .and .x .x3 .x3 .x15, ld .x4 .x8, .adcs .x .x3 .x3 .x4, st .x3 .x5,
        next .x10, next .x8, next .x5] ++ ([.subImm .x .x14 .x14 1] : List Instr))) t
      fun t' => MaInv s₀ B Z eo eN eA c (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t15 : t.gpr .x15 = mask c := (hI.keep.gpr .x15 (by decide)).trans h15
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x8, .x10] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (eo + 8 * j)) ((word t.mem B (eN + 8 * j) &&& mask c) +
        word t.mem B (eA + 8 * j) + BitVec.ofNat 64 t.c.toNat) ∧
      t₁.c = decide (2 ^ 64 ≤ (word t.mem B (eN + 8 * j) &&& mask c).toNat + (word t.mem B (eA + 8 * j)).toNat +
        t.c.toNat) ∧
      t₁.gpr .x10 = off B (eN + 8 * j + 8) ∧ t₁.gpr .x8 = off B (eA + 8 * j + 8) ∧
      t₁.gpr .x5 = off B (eo + 8 * j + 8))
    (by brun [hI.x10, hI.x8, hI.x5, t15, hI.scr.ld (show eN + 8 * j + 8 ≤ Z by omega_using [hN, hj]),
      hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega_using [hA, hj]), hI.scr.st (show eo + 8 * j + 8 ≤ Z by omega_using [ho, hj])])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, hc, h10, h8, h5⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', hc'⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have hx : word t.mem B (eN + 8 * j) = word s₀.mem B (eN + 8 * j) := hI.out.word (by omega_using [sN, hj]) (by omega_using [hN, hj, hn])
  have hy : word t.mem B (eA + 8 * j) = word s₀.mem B (eA + 8 * j) := hI.out.word (by omega_using [sA, hj]) (by omega_using [hA, hj, hn])
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x10 (by decide), h10, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x8 (by decide), h8, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x5 (by decide), h5, Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega_using [ho, hj, hn]) x (by omega_using [hx'])]
    exact hI.out x (by omega_using [hx'])
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega_using [ho, hj, hn]), hc', hc]
    have hs := adcs_toNat (word t.mem B (eN + 8 * j) &&& mask c) (word t.mem B (eA + 8 * j)) t.c
    rw [hx, hy, and_mask] at hs
    have hval := hI.val
    simp only [wv]
    rw [pow64_succ, hx, hy, and_mask]
    cases c
    · simp only [ite_false, Bool.false_eq_true] at hs hval ⊢
      grind
    · simp only [ite_true] at hs hval ⊢
      grind


/-- `addMBody`'s loop, `[x5]` possibly `[x8]`. -/
theorem addMIP_ok {s : State} {B : Addr} {Z N eo eN eA : Nat} {c : Bool} (hs : Scr s B Z)
    (h10 : s.gpr .x10 = off B eN) (h8 : s.gpr .x8 = off B eA) (h5 : s.gpr .x5 = off B eo)
    (h14 : s.gpr .x14 = BitVec.ofNat 64 N) (h15 : s.gpr .x15 = mask c) (hc : s.c = false)
    (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (ho : eo + 8 * N ≤ Z) (hM : eN + 8 * N ≤ Z) (hA : eA + 8 * N ≤ Z)
    (sN : eN + 8 * N ≤ eo ∨ eo + 8 * N ≤ eN) (sA : eo ≤ eA ∨ eA + 8 * N ≤ eo) :
    WP isa (countLoop .x14 addMBody) s fun t =>
      wv t.mem B eo N + 2 ^ (64 * N) * t.c.toNat = (if c then wv s.mem B eN N else 0) + wv s.mem B eA N ∧
      t.gpr .x5 = off B (eo + 8 * N) ∧ Outside B eo (8 * N) s.mem t.mem ∧
      Keep [.x3, .x4, .x5, .x8, .x10, .x14] s t := by
  have h0 : MaInv s B Z eo eN eA c 0 s :=
    ⟨hs, Keep.refl _ _, by rw [h10]; rfl, by rw [h8]; rfl, by rw [h5]; rfl, Outside.refl _ _ _ _,
      by rw [hc]; cases c <;> rfl⟩
  refine WP.mono (wp_countdown (N := N) (by omega_using [hN']) (by omega_using [hN]) (MaInv s B Z eo eN eA c)
    (fun j hj t hI _ => maStepIP_ok h15 ho hM hA sN sA hj hI) h0 h14) fun t hI => ⟨hI.val, hI.x5, hI.out, hI.keep⟩



/-- `topAt j x16`: the address of word `n` of array `j`. -/
theorem topAt_ok {s : State} {B : Addr} {w n : Nat} (j : Nat) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n) (hn : n < 2 ^ 24) :
    WP isa (.block (topAt j .x16)) s fun t =>
      (t.gpr .x16 = off B (slot w j + 8 * n) ∧ t.mem = s.mem ∧ t.v = s.v ∧ t.c = s.c) ∧ Keep [.x3, .x16] s t := by
  unfold topAt
  refine WP.block_append_iff.mpr (WP.mono (WP.vfix (base_ok j .x16 h0 h11)
    (by simp only [Code.allInstrs_eq, instrs, base_vnone])) fun s₁ ⟨⟨⟨h16, m₁, c₁⟩, k₁⟩, v₁⟩ => ?_)
  refine WP.mono (WP.keep [.x3, .x16] (Q := fun t => t.gpr .x16 = off B (slot w j + 8 * n) ∧ t.mem = s₁.mem ∧
      t.v = s₁.v ∧ t.c = s₁.c)
    (by brun [h16, (k₁.gpr .x12 (by decide)).trans h12, shl_ofNat (show n * 2 ^ 3 < 2 ^ 64 by omega_arith),
      RegUpd.v_write, off_add]; congr 2; omega_arith) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h, m, v, c⟩, k⟩ => ⟨⟨h, m.trans m₁, v.trans v₁, c.trans c₁⟩, (k₁.trans k).mono (by decide)⟩

/-- `zeroTop j`: word `n` of array `j` cleared. -/
theorem zeroTop_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (j : Nat) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n) (hn : n ≤ w)
    (hw : w < 2 ^ 24) (hj : j < 16) (hZ : slot w 16 ≤ Z) :
    WP isa (.block (zeroTop j)) s fun t =>
      (t.mem = s.mem.writeW (off B (slot w j + 8 * n)) 0#64 ∧ t.v = s.v ∧ t.c = s.c) ∧ Keep [.x3, .x16] s t := by
  have sj := Nat.le_trans (slot_lt (w := w) hj) hZ
  unfold zeroTop
  refine WP.block_append_iff.mpr (WP.mono (topAt_ok j h0 h11 h12 (by omega_arith)) fun s₁ ⟨⟨h16, m₁, v₁, c₁⟩, k₁⟩ => ?_)
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s.mem.writeW (off B (slot w j + 8 * n)) 0#64 ∧
      t.v = s₁.v ∧ t.c = s₁.c)
    (by brun [h16, (hs.congr k₁.wr).st (show slot w j + 8 * n + 8 ≤ Z by omega_arith), m₁, RegUpd.v_write]; rfl)
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨m, v, c⟩, k⟩ => ⟨⟨m, v.trans v₁, c.trans c₁⟩, (k₁.trans k).mono (by decide)⟩

/-- `signMask j`: the sign mask of word `n` of array `j` into `x15`, `x7 := 0`. -/
theorem signMask_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (j : Nat) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n) (hn : n ≤ w)
    (hw : w < 2 ^ 24) (hj : j < 16) (hZ : slot w 16 ≤ Z) :
    WP isa (.block (signMask j)) s fun t =>
      (t.gpr .x15 = 0#64 - (word s.mem B (slot w j + 8 * n) >>> 63) ∧ t.gpr .x7 = 0 ∧ t.mem = s.mem ∧
        t.v = s.v) ∧ Keep [.x3, .x7, .x15, .x16] s t := by
  have sj := Nat.le_trans (slot_lt (w := w) hj) hZ
  unfold signMask
  refine WP.block_append_iff.mpr (WP.mono (topAt_ok j h0 h11 h12 (by omega_arith)) fun s₁ ⟨⟨h16, m₁, v₁, c₁⟩, k₁⟩ => ?_)
  refine WP.mono (WP.keep [.x3, .x7, .x15] (Q := fun t => t.gpr .x15 = 0#64 - (word s.mem B (slot w j + 8 * n) >>> 63) ∧
      t.gpr .x7 = 0 ∧ t.mem = s₁.mem ∧ t.v = s₁.v)
    (by brun [h16, (hs.congr k₁.wr).ld (show slot w j + 8 * n + 8 ≤ Z by omega_arith), m₁, RegUpd.v_write,
      show BitVec.setWidth 64 0#16 = 0#64 from rfl]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h15, h7, m, v⟩, k⟩ => ⟨⟨h15, h7, m.trans m₁, v.trans v₁⟩, (k₁.trans k).mono (by decide)⟩

/-- The mask of a word even. -/
theorem mask_even (x : BitVec 64) : (x &&& BitVec.setWidth 64 1#16) - 1#64 = mask (decide (x.toNat % 2 = 0)) := by
  have h2 : x &&& BitVec.setWidth 64 1#16 = BitVec.ofNat 64 (x.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (BitVec.setWidth 64 1#16).toNat = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat]
    omega_arith
  rw [h2]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h] <;> decide

/-- The start's first block: `x1`, `x2` into `v19`, words `n` of `f` and `g`
cleared, and what `g`'s masked addition needs. -/
theorem initHead_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n)
    (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iF iG iM : Nat} (hF : iF < 16) (hG : iG < 16)
    (dFG : iF ≠ iG) :
    WP isa (.block (([.vop (.ins .d2 .v19 0 .x1), .vop (.ins .d2 .v19 1 .x2)] : List Instr) ++ zeroTop iF ++ zeroTop iG ++
      base iG .x8 ++ ([ld .x3 .x8, movi .x4 1, .logic .and .x .x3 .x3 .x4, .subImm .x .x15 .x3 1, movi .x7 0,
        mov .x14 .x12, .adds .x .x3 .x7 .x7] : List Instr) ++ base iM .x10 ++ base iG .x5)) s fun t =>
      (t.mem = (s.mem.writeW (off B (slot w iF + 8 * n)) 0#64).writeW (off B (slot w iG + 8 * n)) 0#64 ∧
        laneOf t .v19 0 = s.gpr .x1 ∧ laneOf t .v19 1 = s.gpr .x2 ∧ (∀ r, r ≠ .v19 → t.v r = s.v r) ∧
        t.gpr .x8 = off B (slot w iG) ∧ t.gpr .x5 = off B (slot w iG) ∧ t.gpr .x10 = off B (slot w iM) ∧
        t.gpr .x15 = mask (decide ((word s.mem B (slot w iG)).toNat % 2 = 0)) ∧ t.gpr .x7 = 0 ∧
        t.gpr .x14 = BitVec.ofNat 64 n ∧ t.c = false) ∧
      Keep [.x3, .x4, .x5, .x7, .x8, .x10, .x14, .x15, .x16] s t := by
  have hn' := hs.nowrap
  have sF := Nat.le_trans (slot_lt (w := w) hF) hZ
  have sG := Nat.le_trans (slot_lt (w := w) hG) hZ
  have bv : ∀ j r, (Code.block (base j r) : Prog isa).allInstrs (fun i => (vdstOf i).isNone) = true := fun j r => by
    simp only [Code.allInstrs_eq, instrs, base_vnone]
  simp only [List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [] (Q := fun t => laneOf t .v19 0 = s.gpr .x1 ∧
      laneOf t .v19 1 = s.gpr .x2 ∧ (∀ r, r ≠ .v19 → t.v r = s.v r) ∧ t.mem = s.mem ∧ t.c = s.c)
    (by brun [exec_ins, RegUpd.gpr_setV, RegUpd.mem_setV]
        simp only [reduceCtorEq, ↓reduceIte, laneOf, RegUpd.v_setV, Nat.mul_zero, Nat.mul_one,
          extract_setLane64 _ _ (show (0 : Nat) < 2 by decide) (show (0 : Nat) < 2 by decide),
          extract_setLane64 _ _ (show (1 : Nat) < 2 by decide) (show (0 : Nat) < 2 by decide),
          
          extract_setLane64 _ _ (show (1 : Nat) < 2 by decide) (show (1 : Nat) < 2 by decide), true_and]
        exact ⟨fun r h => by simp only [h, ite_false], rfl⟩) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨l0, l1, lv, m₁, c₁⟩, k₁⟩ => ?_)
  have g0 : s₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h0
  have g11 : s₁.gpr .x11 = _ := (k₁.gpr .x11 (by decide)).trans h11
  have g12 : s₁.gpr .x12 = _ := (k₁.gpr .x12 (by decide)).trans h12
  refine WP.block_append_iff.mpr (WP.mono (zeroTop_ok (hs.congr k₁.wr) iF g0 g11 g12 hn hw hF hZ)
    fun s₂ ⟨⟨m₂, v₂, c₂⟩, k₂⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (zeroTop_ok (hs.congr (k₁.trans k₂).wr) iG
    ((k₂.gpr .x0 (by decide)).trans g0) ((k₂.gpr .x11 (by decide)).trans g11) ((k₂.gpr .x12 (by decide)).trans g12)
    hn hw hG hZ) fun s₃ ⟨⟨m₃, v₃, c₃⟩, k₃⟩ => ?_)
  have k13 := (k₁.trans k₂).trans k₃
  refine WP.block_append_iff.mpr (WP.mono (WP.vfix (base_ok iG .x8 ((k13.gpr .x0 (by decide)).trans h0)
    ((k13.gpr .x11 (by decide)).trans h11)) (bv _ _)) fun s₄ ⟨⟨⟨h8, m₄, c₄⟩, k₄⟩, v₄⟩ => ?_)
  have k14 := k13.trans k₄
  have hm₄ : s₄.mem = (s.mem.writeW (off B (slot w iF + 8 * n)) 0#64).writeW (off B (slot w iG + 8 * n)) 0#64 := by
    rw [m₄, m₃, m₂, m₁]
  have sepFG := slot_apart (w := w) (a := 8) (b := 8 * (n + 1)) dFG.symm (by omega_arith) (by omega_arith)
  have w0 : word s₄.mem B (slot w iG) = word s.mem B (slot w iG) := by
    rw [hm₄, (writeW_outside _ B _ (by omega_arith)).word (by omega_arith) (by omega_arith),
      (writeW_outside _ B _ (by omega_arith)).word (by rcases sepFG with h | h <;> omega_arith) (by omega_arith)]
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x3, .x4, .x7, .x14, .x15] (Q := fun t =>
      t.gpr .x15 = mask (decide ((word s.mem B (slot w iG)).toNat % 2 = 0)) ∧ t.gpr .x7 = 0 ∧
      t.gpr .x14 = BitVec.ofNat 64 n ∧ t.c = false ∧ t.mem = s₄.mem ∧ t.v = s₄.v)
    (by brun [h8, (hs.congr k14.wr).ld (show slot w iG + 8 ≤ Z by omega_arith), (k14.gpr .x12 (by decide)).trans h12,
        RegUpd.v_write, mask_even, w0]
        rfl) (by decide) (by decide) (by decide +kernel)) fun s₅ ⟨⟨h15, h7, h14, c₅, m₅, v₅⟩, k₅⟩ => ?_)
  have k15 := k14.trans k₅
  refine WP.block_append_iff.mpr (WP.mono (WP.vfix (base_ok iM .x10 ((k15.gpr .x0 (by decide)).trans h0)
    ((k15.gpr .x11 (by decide)).trans h11)) (bv _ _)) fun s₆ ⟨⟨⟨h10, m₆, c₆⟩, k₆⟩, v₆⟩ => ?_)
  have k16 := k15.trans k₆
  refine WP.mono (WP.vfix (base_ok iG .x5 ((k16.gpr .x0 (by decide)).trans h0)
    ((k16.gpr .x11 (by decide)).trans h11)) (bv _ _)) fun t ⟨⟨⟨h5, m₇, c₇⟩, k₇⟩, v₇⟩ =>
    ⟨⟨by rw [m₇, m₆, m₅, hm₄], by rw [laneOf, v₇, v₆, v₅, v₄, v₃, v₂]; exact l0,
      by rw [laneOf, v₇, v₆, v₅, v₄, v₃, v₂]; exact l1, fun r hr => by rw [v₇, v₆, v₅, v₄, v₃, v₂]; exact lv r hr,
      (k₇.gpr .x8 (by decide)).trans ((k₆.gpr .x8 (by decide)).trans ((k₅.gpr .x8 (by decide)).trans h8)), h5,
      (k₇.gpr .x10 (by decide)).trans h10, (k₇.gpr .x15 (by decide)).trans ((k₆.gpr .x15 (by decide)).trans h15),
      (k₇.gpr .x7 (by decide)).trans ((k₆.gpr .x7 (by decide)).trans h7),
      (k₇.gpr .x14 (by decide)).trans ((k₆.gpr .x14 (by decide)).trans h14), by rw [c₇, c₆, c₅]⟩,
      ((k16.trans k₇)).mono (by decide)⟩

/-- The start's last block: `b`'s word 0 set, `-(m | 1)⁻¹` into lane 1 of
`v18` and `d = 1` into lane 0, `f`'s word 0 or'ed with 1, and
`x15 := 3 n + 2`. -/
theorem initLast_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iB iM iF : Nat} (hB : iB < 16) (hM : iM < 16)
    (hF : iF < 16) (dBM : iB ≠ iM) (dFB : iF ≠ iB) :
    WP isa (.block (base iB .x16 ++ ([movi .x3 1, st .x3 .x16] : List Instr) ++ base iM .x3 ++
      ([ld .x3 .x3, movi .x4 1, .logic .orr .x .x3 .x3 .x4] : List Instr) ++ minv ++
      ([.vop (.ins .d2 .v18 1 .x15), movi .x3 1, .vop (.ins .d2 .v18 0 .x3)] : List Instr) ++ base iF .x16 ++
      ([ld .x4 .x16, .logic .orr .x .x4 .x4 .x3, st .x4 .x16] : List Instr) ++ batchCount)) s fun t =>
      (t.mem = (s.mem.writeW (off B (slot w iB)) 1#64).writeW (off B (slot w iF))
          (word s.mem B (slot w iF) ||| 1#64) ∧ laneOf t .v18 0 = 1#64 ∧
        ((word s.mem B (slot w iM) ||| 1#64).toNat * (laneOf t .v18 1).toNat + 1) % 2 ^ 64 = 0 ∧
        (∀ r, r ≠ .v18 → t.v r = s.v r) ∧ t.gpr .x15 = BitVec.ofNat 64 (3 * n + 2)) ∧
      Keep [.x3, .x4, .x5, .x6, .x15, .x16] s t := by
  have hn' := hs.nowrap
  have sB := Nat.le_trans (slot_lt (w := w) hB) hZ
  have sM := Nat.le_trans (slot_lt (w := w) hM) hZ
  have sF := Nat.le_trans (slot_lt (w := w) hF) hZ
  have bv : ∀ j r, (Code.block (base j r) : Prog isa).allInstrs (fun i => (vdstOf i).isNone) = true := fun j r => by
    simp only [Code.allInstrs_eq, instrs, base_vnone]
  simp only [List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono (WP.vfix (base_ok iB .x16 h0 h11) (bv _ _))
    fun s₁ ⟨⟨⟨h16, m₁, _⟩, k₁⟩, v₁⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x3] (Q := fun t =>
      t.mem = s.mem.writeW (off B (slot w iB)) 1#64 ∧ t.v = s₁.v)
    (by brun [h16, (hs.congr k₁.wr).st (show slot w iB + 8 ≤ Z by omega_arith), m₁, RegUpd.v_write]; rfl)
    (by decide) (by decide) (by decide +kernel)) fun s₂ ⟨⟨m₂, v₂⟩, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  refine WP.block_append_iff.mpr (WP.mono (WP.vfix (base_ok iM .x3 ((k12.gpr .x0 (by decide)).trans h0)
    ((k12.gpr .x11 (by decide)).trans h11)) (bv _ _)) fun s₃ ⟨⟨⟨h3, m₃, _⟩, k₃⟩, v₃⟩ => ?_)
  have k13 := k12.trans k₃
  have wM : word s₃.mem B (slot w iM) = word s.mem B (slot w iM) := by
    rw [m₃, m₂, (writeW_outside _ B _ (by omega_arith)).word (by
      rcases slot_apart (w := w) (a := 8) (b := 8) dBM.symm (by omega_arith) (by omega_arith) with h | h <;> omega_arith) (by omega_arith)]
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x3, .x4] (Q := fun t =>
      t.gpr .x3 = word s.mem B (slot w iM) ||| 1#64 ∧ t.mem = s₃.mem ∧ t.v = s₃.v)
    (by brun [h3, (hs.congr k13.wr).ld (show slot w iM + 8 ≤ Z by omega_arith), wM, RegUpd.v_write]; rfl)
    (by decide) (by decide) (by decide +kernel)) fun s₄ ⟨⟨h3', m₄, v₄⟩, k₄⟩ => ?_)
  have k14 := k13.trans k₄
  have odd : (s₄.gpr .x3).toNat % 2 = 1 := by
    rw [h3', BitVec.toNat_or, BitVec.toNat_ofNat]
    exact Nat.or_mod_two_eq_one.mpr (.inr rfl)
  refine WP.block_append_iff.mpr (WP.mono (WP.vfix (minv_ok s₄ odd) (by decide +kernel))
    fun s₅ ⟨⟨hmi, k₅, m₅⟩, v₅⟩ => ?_)
  have k15 := k14.trans k₅
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x3] (Q := fun t => laneOf t .v18 0 = 1#64 ∧
      laneOf t .v18 1 = s₅.gpr .x15 ∧ (∀ r, r ≠ .v18 → t.v r = s₅.v r) ∧ t.mem = s₅.mem ∧ t.gpr .x3 = 1#64)
    (by
      brun [exec_ins, RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.v_write]
      simp only [reduceCtorEq, ↓reduceIte, laneOf, RegUpd.v_write, RegUpd.v_setV, Nat.mul_zero,
        Nat.mul_one, extract_setLane64 _ _ (show (0 : Nat) < 2 by decide) (show (0 : Nat) < 2 by decide),
        extract_setLane64 _ _ (show (0 : Nat) < 2 by decide) (show (1 : Nat) < 2 by decide),
        extract_setLane64 _ _ (show (1 : Nat) < 2 by decide) (show (1 : Nat) < 2 by decide), true_and]
      exact ⟨rfl, fun r h => by simp only [h, ite_false]⟩) (by decide) (by decide) (by decide +kernel))
    fun s₆ ⟨⟨l0, l1, lv, m₆, h3₆⟩, k₆⟩ => ?_)
  have k16 := k15.trans k₆
  refine WP.block_append_iff.mpr (WP.mono (WP.vfix (base_ok iF .x16 ((k16.gpr .x0 (by decide)).trans h0)
    ((k16.gpr .x11 (by decide)).trans h11)) (bv _ _)) fun s₇ ⟨⟨⟨h16₇, m₇, _⟩, k₇⟩, v₇⟩ => ?_)
  have k17 := k16.trans k₇
  have hm₇ : s₇.mem = s.mem.writeW (off B (slot w iB)) 1#64 := by rw [m₇, m₆, m₅, m₄, m₃, m₂]
  have wF : word s₇.mem B (slot w iF) = word s.mem B (slot w iF) := by
    rw [hm₇, (writeW_outside _ B _ (by omega_arith)).word (by
      rcases slot_apart (w := w) (a := 8) (b := 8) dFB (by omega_arith) (by omega_arith) with h | h <;> omega_arith) (by omega_arith)]
  refine WP.mono (WP.keep [.x4, .x15] (Q := fun t => t.mem = s₇.mem.writeW (off B (slot w iF))
      (word s.mem B (slot w iF) ||| 1#64) ∧ t.v = s₇.v ∧ t.gpr .x15 = BitVec.ofNat 64 (3 * n + 2))
    (by
      unfold batchCount
      brun [h16₇, (hs.congr k17.wr).ld (show slot w iF + 8 ≤ Z by omega_arith),
        (hs.congr k17.wr).st (show slot w iF + 8 ≤ Z by omega_arith), wF, (k₇.gpr .x3 (by decide)).trans h3₆,
        RegUpd.v_write, (k17.gpr .x12 (by decide)).trans h12]
      simp only [off, BitVec.ofNat_add_ofNat]
      congr 1; omega_arith) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨m₈, v₈, h15⟩, k₈⟩ =>
    ⟨⟨by rw [m₈, hm₇], by rw [laneOf, v₈, v₇, ← laneOf]; exact l0,
      by rw [laneOf, v₈, v₇, ← laneOf, l1, ← h3']; exact hmi,
      fun r hr => by rw [v₈, v₇, lv r hr, v₅, v₄, v₃, v₂, v₁], h15⟩, (k17.trans k₈).mono (by decide)⟩
end VG.Proof.Rsa.AArch64

-- From `Proof/Rsa/AArch64/InvInit.lean`.
/-!
# RSA private keys on AArch64: the start of the batched inverse

`batchInit_ok`: `Keys.batchInit` leaves `LInv` before any batch: `f = m`
(its word `n` cleared), `g = a + (m if a is even)` (`Divstep.oddInput`,
the masked addition in place), `a = 0` and `b = 1` (`n + 2` words),
`d = 1`, `-m⁻¹ mod 2^64` (unique: `minv_unique`) in the lanes of `v18`,
`x1`, `x2` in those of `v19`, and the batches counted in `x15`.
-/


namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.InvBatch
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Divstep (sgn)

/-- `x | 1` adds the missing low bit. -/
theorem or_one_eq (x : Nat) : x ||| 1 = x + (1 - x % 2) := by
  have h1 : (x ||| 1) / 2 = x / 2 := by rw [Nat.or_div_two]; simp
  have h2 : (x ||| 1) % 2 = 1 := Nat.or_mod_two_eq_one.mpr (.inr rfl)
  omega_arith

/-- Word 0 of a number or'ed with 1. -/
theorem wv_or1 (m : Mem) (B : Addr) {d k : Nat} (h : d + 8 * (k + 1) ≤ 2 ^ 64) :
    wv (m.writeW (off B d) (word m B d ||| 1#64)) B d (k + 1) =
      wv m B d (k + 1) + (1 - wv m B d (k + 1) % 2) := by
  rw [Nat.add_comm k 1, wv_add, wv_add m]
  rw [(writeW_outside m B _ (by omega_arith)).wv (d := d + 8 * 1) (k := k) (Or.inr (by omega_arith)) (by omega_arith)]
  have e1 : ∀ m' : Mem, wv m' B d 1 = (word m' B d).toNat := fun m' => by simp [wv]
  rw [e1, e1, word_writeW_self, BitVec.toNat_or, BitVec.toNat_ofNat, show 1 % 2 ^ 64 = 1 from rfl, or_one_eq]
  have := (word m B d).isLt
  omega_arith

/-- `-p⁻¹ mod 2^64` is unique. -/
theorem minv_unique {p a b : Nat} (hp : p % 2 = 1) (ha : (p * a + 1) % 2 ^ 64 = 0) (hb : (p * b + 1) % 2 ^ 64 = 0)
    (ha' : a < 2 ^ 64) (hb' : b < 2 ^ 64) : a = b := by
  have hc : Nat.Coprime (2 ^ 64) p := Nat.Coprime.pow_left _ (by
    show Nat.gcd 2 p = 1
    rw [Nat.gcd_rec, hp]; rfl)
  wlog h : a ≤ b
  · exact (this hp hb ha hb' ha' hc (by omega_arith)).symm
  have hd : 2 ^ 64 ∣ p * (b - a) := by
    rw [Nat.mul_sub]
    have := Nat.sub_mod_eq_zero_of_mod_eq (show (p * b + 1) % 2 ^ 64 = (p * a + 1) % 2 ^ 64 by omega_arith)
    rw [show p * b + 1 - (p * a + 1) = p * b - p * a by omega_arith] at this
    exact Nat.dvd_of_mod_eq_zero this
  obtain ⟨k, hk⟩ := hc.dvd_of_dvd_mul_left hd
  rcases k with _ | k
  · omega_arith
  · have : 2 ^ 64 * (k + 1) ≥ 2 ^ 64 := Nat.le_mul_of_pos_right _ (by omega_arith)
    omega_arith

/-- Word `n` of an array is apart from the first `n` words of each. -/
theorem top_apart {w n : Nat} (j X : Nat) (hn : n ≤ w) :
    slot w j + 8 * n ≤ slot w X + 8 * n ∨ slot w X + 8 * n + 8 ≤ slot w j := by
  by_cases h : j = X
  · subst h; exact .inl (Nat.le_refl _)
  · rcases slot_apart (w := w) (a := 8 * n) (b := 8 * n + 8) h (by omega_arith) (by omega_arith) with h' | h' <;> omega_arith

/-- A prefix of a zero number is zero. -/
theorem wv_zero_prefix {m : Mem} {B : Addr} {d k j : Nat} (h : wv m B d (k + j) = 0) : wv m B d k = 0 := by
  rw [wv_add] at h; omega_arith

/-- A signed number of `n + 1` words below `2^(64 n + 1)` is its value. -/
theorem sgn_small {n x : Nat} (hx : x < 2 ^ (64 * n + 1)) : sgn (n + 1) x = x := by
  unfold sgn
  rw [ite_eq_left (show x < 2 ^ (64 * (n + 1) - 1) from Nat.lt_of_lt_of_le hx
    (Nat.pow_le_pow_right (by decide) (by omega_arith)))]

/-- The start: `f = m`, `g = a + (m if a is even)`, `a = 0`, `b = 1`,
`d = 1`, `-m⁻¹`, `x1`, `x2` saved, and the batches counted. -/
theorem batchInit_ok {C : ICfg} (hC : C.Ok) {s : State} {a : Nat} (hs : Scr s C.B C.Z) (h0 : s.gpr .x0 = C.B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (C.w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 C.n)
    (hV : wv s.mem C.B (slot C.w C.iV) C.n = C.p) (hM : wv s.mem C.B (slot C.w C.iM) C.n = C.p)
    (hU : wv s.mem C.B (slot C.w C.iU) C.n = a) (hx : C.x = Rsa.Divstep.oddInput C.p a) :
    WP isa (seqs (batchInit C.iV C.iU C.iX₂ C.iX₁ C.iM)) s fun t =>
      LInv C s 0 t ∧ t.gpr .x15 = BitVec.ofNat 64 (3 * C.n + 2) := by
  have hn' := hs.nowrap
  have hn1 := hC.n1; have hnw := hC.nw; have hw := hC.w24; have hZ := hC.hZ
  have sl : ∀ j < 16, slot C.w j + 8 * (C.w + 2) ≤ C.Z := fun j hj => Nat.le_trans (slot_lt (w := C.w) hj) hZ
  have sV := sl _ hC.hV; have sU := sl _ hC.hU; have sM := sl _ hC.hM; have sX₁ := sl _ hC.hX₁
  have sX₂ := sl _ hC.hX₂
  simp only [batchInit, seqs]
  refine WP.seq (WP.mono (initHead_ok hs h0 h11 h12 hn1 hnw hw hZ hC.hV hC.hU hC.dUV.symm)
    fun s₁ ⟨⟨m₁, l0, l1, lv, h8, h5, h10, h15, h7, h14, hc⟩, k₁⟩ => ?_)
  -- The first `n` words of `g` and `m` as on entry.
  have sepUM := slot_apart (w := C.w) (a := 8 * C.n) (b := 8 * C.n) hC.dUM (by omega_arith) (by omega_arith)
  have o₁ : ∀ {j : Nat}, j < 16 → wv s₁.mem C.B (slot C.w j) C.n = wv s.mem C.B (slot C.w j) C.n := fun {j} hj => by
    rw [m₁, (writeW_outside _ C.B _ (by omega_arith)).wv (top_apart j C.iU hnw) (by have := sl _ hj; omega_arith),
      (writeW_outside _ C.B _ (by omega_arith)).wv (top_apart j C.iV hnw) (by have := sl _ hj; omega_arith)]
  have k1 := k₁
  -- `g += m` if `a` is even.
  refine WP.seq (WP.mono (WP.vfix (addMIP_ok (N := C.n) (hs.congr k₁.wr) h10 h8 h5 h14 h15 hc hn1 (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by rcases sepUM with h | h <;> omega_arith) (.inl (Nat.le_refl _))) (by decide +kernel))
    fun s₂ ⟨⟨e₂, h5', o₂, k₂⟩, v₂⟩ => ?_)
  rw [o₁ hC.hM, o₁ hC.hU, hM, hU] at e₂
  have k12 := k₁.trans k₂
  have g7 : s₂.gpr .x7 = 0 := (k₂.gpr .x7 (by decide)).trans h7
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s₂.mem.writeW (off C.B (slot C.w C.iU + 8 * C.n))
      (BitVec.ofNat 64 s₂.c.toNat) ∧ t.v = s₂.v)
    (by brun [g7, h5', (hs.congr k12.wr).st (show slot C.w C.iU + 8 * C.n + 8 ≤ C.Z by omega_arith), RegUpd.v_write]
        rw [zero_add64, zero_add64])
    (by decide) (by decide) (by decide +kernel)) fun s₃ ⟨⟨m₃, v₃⟩, k₃⟩ => ?_)
  have par : (word s.mem C.B (slot C.w C.iU)).toNat % 2 = a % 2 := by
    rw [← wv_mod64 _ _ _ hn1, hU, Nat.mod_mod_of_dvd _ (by decide)]
  have gU : wv s₃.mem C.B (slot C.w C.iU) (C.n + 1) = C.x := by
    rw [m₃, wv_writeW_top _ _ _ _ _ (by omega_arith), hx, Rsa.Divstep.oddInput, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by cases s₂.c <;> decide)]
    rw [par] at e₂
    by_cases h : a % 2 = 0
    · simp only [h, decide_true, ite_true] at e₂ ⊢
      rw [e₂, Nat.add_comm]
    · simp only [h, decide_false, Bool.false_eq_true, ite_false, Nat.zero_add, Nat.add_zero] at e₂ ⊢
      exact e₂
  have k13 := k12.trans k₃
  have zA : ∀ {j : Nat} {s' : State}, j < 16 → Scr s' C.B C.Z → s'.gpr .x0 = C.B →
      s'.gpr .x11 = BitVec.ofNat 64 (8 * (C.w + 2)) → s'.gpr .x12 = BitVec.ofNat 64 C.n →
      WP isa (.seq (.block (base j .x8 ++ ([movi .x7 0] : List Instr))) zeroAcc) s' fun t =>
        wv t.mem C.B (slot C.w j) (C.n + 2) = 0 ∧ Outside C.B (slot C.w j) (8 * (C.n + 2)) s'.mem t.mem ∧
        Keep [.x7, .x8, .x14, .x16] s' t ∧ t.v = s'.v := fun {j s'} hj hs' g0 g11 g12 => by
    refine WP.mono (WP.vfix (Q := fun t => wv t.mem C.B (slot C.w j) (C.n + 2) = 0 ∧
      Outside C.B (slot C.w j) (8 * (C.n + 2)) s'.mem t.mem ∧ Keep [.x7, .x8, .x14, .x16] s' t) ?_
      (by simp only [Code.allInstrs_eq, instrs, List.all_append, base_vnone, zeroAcc, countLoop]; decide))
      fun t ⟨a, v⟩ => ⟨a.1, a.2.1, a.2.2, v⟩
    refine WP.seq (WP.block_append_iff.mpr (WP.mono (base_ok j .x8 g0 g11) fun t₁ ⟨⟨h8', m₁', _⟩, k₁'⟩ =>
      WP.mono (WP.keep [.x7] (Q := fun t => t.gpr .x7 = 0 ∧ t.mem = t₁.mem) (by brun) (by decide) (by decide)
        (by decide +kernel)) fun t₂ ⟨⟨h7', m₂'⟩, k₂'⟩ => ?_))
    have k12' := k₁'.trans k₂'
    refine WP.mono (zeroAcc_ok (hs'.congr k12'.wr) ((k₂'.gpr .x8 (by decide)).trans h8') ((k12'.gpr .x12 (by decide)).trans g12)
      h7' (by omega_arith) (by have := sl _ hj; omega_arith)) fun t ⟨z, o, k⟩ => ⟨z, by rw [m₂', m₁'] at o; exact o,
        (k12'.trans k).mono (by decide)⟩
  refine WP.seq (WP.mono (zA hC.hX₂ (hs.congr k13.wr) ((k13.gpr .x0 (by decide)).trans h0)
    ((k13.gpr .x11 (by decide)).trans h11) ((k13.gpr .x12 (by decide)).trans h12)) fun s₄ ⟨z₄, o₄, k₄, v₄⟩ => ?_)
  have k14 := k13.trans k₄
  refine WP.seq (WP.mono (zA hC.hX₁ (hs.congr k14.wr) ((k14.gpr .x0 (by decide)).trans h0)
    ((k14.gpr .x11 (by decide)).trans h11) ((k14.gpr .x12 (by decide)).trans h12)) fun s₅ ⟨z₅, o₅, k₅, v₅⟩ => ?_)
  have k15 := k14.trans k₅
  have hp := wv_lt s.mem C.B (slot C.w C.iM) C.n
  rw [hM] at hp
  -- From `s₁` on, only `g`, `a` and `b` change.
  have f2 : Frm C.B [(slot C.w C.iU, 8 * (C.w + 2)), (slot C.w C.iX₂, 8 * (C.w + 2)),
      (slot C.w C.iX₁, 8 * (C.w + 2))] s₁.mem s₂.mem :=
    Frm.of_outside (Outside.mono (o' := slot C.w C.iU) (n' := 8 * (C.w + 2)) o₂ (Nat.le_refl _) (by omega_arith)) (by simp)
  have f3 : Frm C.B [(slot C.w C.iU, 8 * (C.w + 2)), (slot C.w C.iX₂, 8 * (C.w + 2)),
      (slot C.w C.iX₁, 8 * (C.w + 2))] s₂.mem s₃.mem := by
    rw [m₃]; exact Frm.of_outside (Outside.mono (o' := slot C.w C.iU) (n' := 8 * (C.w + 2))
      (writeW_outside _ C.B _ (by omega_arith)) (by omega_arith) (by omega_arith)) (by simp)
  have f4 : Frm C.B [(slot C.w C.iU, 8 * (C.w + 2)), (slot C.w C.iX₂, 8 * (C.w + 2)),
      (slot C.w C.iX₁, 8 * (C.w + 2))] s₃.mem s₄.mem :=
    Frm.of_outside (Outside.mono (o' := slot C.w C.iX₂) (n' := 8 * (C.w + 2)) o₄ (Nat.le_refl _) (by omega_arith)) (by simp)
  have f5 : Frm C.B [(slot C.w C.iU, 8 * (C.w + 2)), (slot C.w C.iX₂, 8 * (C.w + 2)),
      (slot C.w C.iX₁, 8 * (C.w + 2))] s₄.mem s₅.mem :=
    Frm.of_outside (Outside.mono (o' := slot C.w C.iX₁) (n' := 8 * (C.w + 2)) o₅ (Nat.le_refl _) (by omega_arith)) (by simp)
  have f15 := ((f2.trans f3).trans f4).trans f5
  have apM := apart3 (w := C.w) (L := C.n) hC.dUM.symm hC.dX₂M.symm hC.dX₁M.symm (by omega_arith) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _)
  have M₅ : wv s₅.mem C.B (slot C.w C.iM) C.n = C.p := by
    rw [f15.wv_eq apM (by omega_arith), o₁ hC.hM, hM]
  refine WP.mono (initLast_ok (hs.congr k15.wr) ((k15.gpr .x0 (by decide)).trans h0)
    ((k15.gpr .x11 (by decide)).trans h11) ((k15.gpr .x12 (by decide)).trans h12) hnw hw hZ hC.hX₁ hC.hM hC.hV
    hC.dX₁M hC.dVX₁) fun t ⟨⟨m₆, l0', lmi, lv', h15'⟩, k₆⟩ => ?_
  have k16 := k15.trans k₆
  have hZ' : slot C.w 16 + C.B.toNat ≤ 2 ^ 64 := by omega_arith
  set mid := s₅.mem.writeW (off C.B (slot C.w C.iX₁)) 1#64 with hmid
  have o₆a : Outside C.B (slot C.w C.iX₁) 8 s₅.mem mid := writeW_outside _ C.B _ (by omega_arith)
  have sVX := slot_apart (w := C.w) (a := 8) (b := 8) hC.dVX₁ (by omega_arith) (by omega_arith)
  have wVm : word s₅.mem C.B (slot C.w C.iV) = word mid C.B (slot C.w C.iV) :=
    (o₆a.word (by rcases sVX with h | h <;> omega_arith) (by omega_arith)).symm
  rw [wVm] at m₆
  have o₆b : Outside C.B (slot C.w C.iV) 8 mid t.mem := by rw [m₆]; exact writeW_outside _ C.B _ (by omega_arith)
  have f6 : Frm C.B C.ranges s₅.mem t.mem :=
    (Frm.of_outside (Outside.mono (o' := slot C.w C.iX₁) (n' := 8 * (C.w + 2)) o₆a (by omega_arith) (by omega_arith))
      (by simp [ICfg.ranges])).trans
    (Frm.of_outside (Outside.mono (o' := slot C.w C.iV) (n' := 8 * (C.w + 2)) o₆b (by omega_arith) (by omega_arith))
      (by simp [ICfg.ranges]))
  -- Arrays other than `f`, `a` and `b` from `s₃` on.
  have late : ∀ {j : Nat} {L : Nat}, j ≠ C.iX₂ → j ≠ C.iX₁ → j ≠ C.iV → L ≤ C.w + 2 → j < 16 →
      wv t.mem C.B (slot C.w j) L = wv s₃.mem C.B (slot C.w j) L := fun {j L} a b c hL hj => by
    rw [wv_out o₆b c.symm (by omega_arith) hL hZ' hj, wv_out o₆a b.symm (by omega_arith) hL hZ' hj,
      wv_out o₅ b.symm (by omega_arith) hL hZ' hj, wv_out o₄ a.symm (by omega_arith) hL hZ' hj]
  have sVU := slot_apart (w := C.w) (a := 8 * (C.n + 1)) (b := 8 * C.n + 8) hC.dUV.symm (by omega_arith) (by omega_arith)
  have sVU0 := slot_apart (w := C.w) (a := 8 * (C.n + 1)) (b := 8 * C.n) hC.dUV.symm (by omega_arith) (by omega_arith)
  have V21 : wv s₂.mem C.B (slot C.w C.iV) (C.n + 1) = wv s₁.mem C.B (slot C.w C.iV) (C.n + 1) :=
    o₂.wv (by rcases sVU0 with h | h <;> omega_arith) (by omega_arith)
  -- `f = m` before its low bit is set.
  have fV₃ : wv s₃.mem C.B (slot C.w C.iV) (C.n + 1) = C.p := by
    rw [m₃, (writeW_outside _ C.B _ (by omega_arith)).wv
      (by rcases sVU with h | h <;> omega_arith) (by omega_arith), V21, m₁,
      (writeW_outside _ C.B _ (by omega_arith)).wv (by rcases sVU with h | h <;> omega_arith) (by omega_arith),
      wv_writeW_top _ _ _ _ _ (by omega_arith), hV]
    rfl
  have fVm : wv mid C.B (slot C.w C.iV) (C.n + 1) = C.p := by
    rw [wv_out o₆a hC.dVX₁.symm (by omega_arith) (by omega_arith) hZ' hC.hV,
      wv_out o₅ hC.dVX₁.symm (by omega_arith) (by omega_arith) hZ' hC.hV, wv_out o₄ hC.dVX₂.symm (by omega_arith) (by omega_arith) hZ' hC.hV,
      fV₃]
  have fV : wv t.mem C.B (slot C.w C.iV) (C.n + 1) = C.pf := by
    rw [m₆, wv_or1 _ _ (by omega_arith), fVm]; rfl
  -- `g`.
  have gU' : wv t.mem C.B (slot C.w C.iU) (C.n + 1) = C.x := by
    rw [late hC.dUX₂ hC.dUX₁ hC.dUV (by omega_arith) hC.hU, gU]
  have aX : wv t.mem C.B (slot C.w C.iX₂) (C.n + 1) = 0 := by
    rw [wv_out o₆b hC.dVX₂ (by omega_arith) (by omega_arith) hZ' hC.hX₂, wv_out o₆a hC.dX (by omega_arith) (by omega_arith) hZ' hC.hX₂,
      wv_out o₅ hC.dX (by omega_arith) (by omega_arith) hZ' hC.hX₂]
    exact wv_zero_prefix (j := 1) z₄
  have bX : wv t.mem C.B (slot C.w C.iX₁) (C.n + 1) = 1 := by
    rw [wv_out o₆b hC.dVX₁ (by omega_arith) (by omega_arith) hZ' hC.hX₁]
    have e := wv_add mid C.B (slot C.w C.iX₁) 1 C.n
    have z := wv_add s₅.mem C.B (slot C.w C.iX₁) 1 (C.n + 1)
    rw [show 1 + (C.n + 1) = C.n + 2 by omega_arith, z₅] at z
    have z' : wv s₅.mem C.B (slot C.w C.iX₁ + 8 * 1) C.n = 0 := wv_zero_prefix (j := 1) (by omega_arith)
    rw [Nat.add_comm 1 C.n] at e
    rw [e, hmid, (writeW_outside _ C.B _ (by omega_arith)).wv (d := slot C.w C.iX₁ + 8 * 1) (k := C.n) (by omega_arith) (by omega_arith), z']
    simp only [wv, Nat.mul_zero, Nat.add_zero, word_writeW_self, Nat.zero_add, Nat.pow_zero, Nat.one_mul]; rfl
  have hpN : C.pf < 2 ^ (64 * C.n + 1) := by have := hC.pC; unfold ICfg.pf; rw [Nat.pow_succ]; omega_arith
  have v15 : t.v .v19 = s₁.v .v19 := by rw [lv' _ (by decide), v₅, v₄, v₃, v₂]
  have hw0 : (word s₅.mem C.B (slot C.w C.iM) ||| 1#64).toNat = C.pf % 2 ^ 64 := by
    rw [BitVec.toNat_or, BitVec.toNat_ofNat, show 1 % 2 ^ 64 = 1 from rfl, or_one_eq, ← wv_mod64 _ _ _ hn1, M₅]
    have := hC.pC
    unfold ICfg.pf
    have h64 : C.p % 2 ^ 64 % 2 = C.p % 2 := Nat.mod_mod_of_dvd _ (by decide)
    have : C.p % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
    rw [h64]
    omega_arith
  refine ⟨⟨hs.congr k16.wr, (k16.gpr .x0 (by decide)).trans h0, (k16.gpr .x11 (by decide)).trans h11,
    (k16.gpr .x12 (by decide)).trans h12,
    by rw [fV, sgn_small hpN]; simp only [ICfg.st, Divstep.invRunS],
    by rw [gU', sgn_small hC.xC]; simp only [ICfg.st, Divstep.invRunS],
    fun _ => by rw [aX, sgn_small (Nat.two_pow_pos (64 * C.n + 1))]; simp only [ICfg.st, Divstep.invRunS]; rfl,
    fun _ => by rw [bX, sgn_small (Nat.one_lt_two_pow (by omega_arith))]; simp only [ICfg.st, Divstep.invRunS]; rfl,
    by rw [l0']; simp only [ICfg.st, Divstep.invRunS]; decide, ?_, ?_, ?_, k16.mono (by decide),
    by rw [laneOf, v15, ← laneOf, l0], by rw [laneOf, v15, ← laneOf, l1]⟩, h15'⟩
  · apply BitVec.eq_of_toNat_eq
    refine minv_unique (p := C.pf % 2 ^ 64) (by unfold ICfg.pf; omega_arith) (by rw [← hw0]; exact lmi) ?_
      (BitVec.isLt _) (BitVec.isLt _)
    have := hC.hm
    have h' : (C.pf * C.mi.toNat + 1) % 2 ^ 64 = 0 := by unfold ICfg.pf; exact_mod_cast this
    rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]; exact h'
  · rw [wv_out o₆b hC.dVM (by omega_arith) (by omega_arith) hZ' hC.hM, wv_out o₆a hC.dX₁M (by omega_arith) (by omega_arith) hZ' hC.hM,
      M₅]
  · have f01 : Frm C.B C.ranges s.mem s₁.mem := by
      rw [m₁]
      exact (Frm.of_outside (Outside.mono (o' := slot C.w C.iV) (n' := 8 * (C.w + 2))
        (writeW_outside _ C.B _ (by omega_arith)) (by omega_arith) (by omega_arith)) (by simp [ICfg.ranges])).trans
        (Frm.of_outside (Outside.mono (o' := slot C.w C.iU) (n' := 8 * (C.w + 2))
        (writeW_outside _ C.B _ (by omega_arith)) (by omega_arith) (by omega_arith)) (by simp [ICfg.ranges]))
    exact (f01.trans (Frm.widen f15 (fun r hr => ⟨r, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [ICfg.ranges], Nat.le_refl _, Nat.le_refl _⟩))).trans f6
end VG.Proof.Rsa.AArch64

-- From `Proof/Rsa/AArch64/InvEnd.lean`.
/-!
# RSA private keys on AArch64: the pieces of the batched inverse's end

`cnegP_ok`: `[x] := -[x]` where a mask says so, by `cnegBody` in place
(`cnegLoop_ok`); `addIfNeg_ok`: `[a] += m` if `[a]` is negative (the masked
addition in place, then the top word); `csubP_ok`: `[a] mod m` for
`[a] < 2 m` (`subMod`, `selectAcc` in place: `selectAccIP_ok`).
-/


namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.InvBatch
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- A word of `cnegBody`'s value: `(x ^ m) + C`. -/
theorem xor_mask (x : BitVec 64) (neg : Bool) :
    (x ^^^ mask neg).toNat = if neg then 2 ^ 64 - 1 - x.toNat else x.toNat := by
  cases neg
  · simp [mask_false]
  · simp only [mask_true, ite_true, BitVec.xor_allOnes, BitVec.toNat_not]

/-- After `j` words of `cnegBody` in place. -/
structure CnegInv (s₀ : State) (B : Addr) (Z eX : Nat) (neg : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x14, .x16] s₀ t
  x16 : t.gpr .x16 = off B (eX + 8 * j)
  out : Outside B eX (8 * j) s₀.mem t.mem
  val : wv t.mem B eX j + 2 ^ (64 * j) * t.c.toNat =
    (if neg then 2 ^ (64 * j) - 1 - wv s₀.mem B eX j else wv s₀.mem B eX j) + neg.toNat

theorem cnegLoop_ok {s : State} {B : Addr} {Z L eX : Nat} {neg : Bool} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eX) (h14 : s.gpr .x14 = BitVec.ofNat 64 L) (h15 : s.gpr .x15 = mask neg)
    (h7 : s.gpr .x7 = 0) (hc : s.c = neg) (hL : 1 ≤ L) (hL' : L < 2 ^ 32) (hX : eX + 8 * L ≤ Z) :
    WP isa (countLoop .x14 cnegBody) s (CnegInv s B Z eX neg L) := by
  have hn := hs.nowrap
  have h0 : CnegInv s B Z eX neg 0 s :=
    ⟨hs, Keep.refl _ _, by rw [h16]; rfl, Outside.refl _ _ _ _, by cases neg <;> simp [wv, hc]⟩
  refine wp_countdown (N := L) (by omega_arith) (by omega_arith) (CnegInv s B Z eX neg) (fun j hj t hI _ => ?_) h0 h14
  have t15 : t.gpr .x15 = mask neg := (hI.keep.gpr .x15 (by decide)).trans h15
  have t7 : t.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans h7
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x16] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (eX + 8 * j)) ((word t.mem B (eX + 8 * j) ^^^ mask neg) + 0 +
        BitVec.ofNat 64 t.c.toNat) ∧
      t₁.c = decide (2 ^ 64 ≤ (word t.mem B (eX + 8 * j) ^^^ mask neg).toNat + (0 : BitVec 64).toNat + t.c.toNat) ∧
      t₁.gpr .x16 = off B (eX + 8 * j + 8))
    (by unfold cnegBody; brun [hI.x16, t15, t7, hI.scr.ld (show eX + 8 * j + 8 ≤ Z by omega_arith),
      hI.scr.st (show eX + 8 * j + 8 ≤ Z by omega_arith)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, hc', h16'⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14', hm', hc''⟩, k'⟩ => ⟨?_, by rw [h14', k₁.gpr .x14 (by decide)]⟩
  have hx : word t.mem B (eX + 8 * j) = word s.mem B (eX + 8 * j) := hI.out.word (by omega_arith) (by omega_arith)
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16', Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega_arith) x (by omega_arith)]
    exact hI.out x (by omega_arith)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega_arith), hc'', hc']
    have hval := hI.val
    have xm := xor_mask (word s.mem B (eX + 8 * j)) neg
    rw [hx]
    simp only [wv]
    have hW := wv_lt s.mem B eX j
    have hw := (word s.mem B (eX + 8 * j)).isLt
    rw [pow64_succ]
    have ad := adcs_toNat (word s.mem B (eX + 8 * j) ^^^ mask neg) 0 t.c
    rw [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at ad
    rw [show BitVec.toNat (0 : BitVec 64) = 0 from rfl, Nat.add_zero, Nat.mul_assoc, Nat.add_assoc,
      ← Nat.mul_add, ad, xm]
    generalize hP : 2 ^ (64 * j) = P at *
    have hP1 : 1 ≤ P := by rw [← hP]; exact Nat.one_le_two_pow
    have hc1 := Bool.toNat_le t.c
    cases neg
    · simp only [Bool.false_eq_true, ite_false, Bool.toNat_false, Nat.add_zero] at hval ⊢
      rw [Nat.mul_add]; omega_arith
    · simp only [ite_true, Bool.toNat_true] at hval ⊢
      have e1 : P * (2 ^ 64 - 1 - (word s.mem B (eX + 8 * j)).toNat + t.c.toNat) =
          P * 2 ^ 64 - P - P * (word s.mem B (eX + 8 * j)).toNat + P * t.c.toNat := by
        rw [Nat.mul_add, Nat.mul_sub, Nat.mul_sub, Nat.mul_one]
      have e2 : P * (word s.mem B (eX + 8 * j)).toNat ≤ P * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega_arith)
      rw [Nat.mul_sub, Nat.mul_one] at e2
      have e3 : P ≤ P * 2 ^ 64 := Nat.le_mul_of_pos_right _ (by decide)
      rw [e1]; omega_arith

/-- `cnegP x`: `[x] := -[x]` (`n + 1` words) where `x15` is the mask of `neg`. -/
theorem cnegP_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iX : Nat} (hX : iX < 16) {neg : Bool}
    (h15 : s.gpr .x15 = mask neg) :
    WP isa (cnegP iX) s fun t =>
      wv t.mem B (slot w iX) (n + 1) + 2 ^ (64 * (n + 1)) * t.c.toNat =
        (if neg then 2 ^ (64 * (n + 1)) - 1 - wv s.mem B (slot w iX) (n + 1) else wv s.mem B (slot w iX) (n + 1)) +
          neg.toNat ∧
      Outside B (slot w iX) (8 * (n + 1)) s.mem t.mem ∧ Keep [.x3, .x7, .x14, .x16] s t ∧ t.v = s.v := by
  have hn' := hs.nowrap
  have sX := Nat.le_trans (slot_lt (w := w) hX) hZ
  have hvn : (cnegP iX).allInstrs (fun i => (vdstOf i).isNone) = true := by
    simp only [cnegP, Code.allInstrs_eq, instrs, List.all_append, base_vnone]; decide
  refine WP.mono (WP.vfix (Q := fun t => wv t.mem B (slot w iX) (n + 1) + 2 ^ (64 * (n + 1)) * t.c.toNat =
        (if neg then 2 ^ (64 * (n + 1)) - 1 - wv s.mem B (slot w iX) (n + 1) else wv s.mem B (slot w iX) (n + 1)) +
          neg.toNat ∧
      Outside B (slot w iX) (8 * (n + 1)) s.mem t.mem ∧ Keep [.x3, .x7, .x14, .x16] s t) ?_ hvn)
    fun t ⟨⟨a, b, c⟩, v⟩ => ⟨a, b, c, v⟩
  unfold cnegP
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (base_ok iX .x16 h0 h11) fun s₁ ⟨⟨h16, m₁, _⟩, k₁⟩ =>
    WP.mono (WP.keep [.x3, .x7, .x14] (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 (n + 1) ∧ t.gpr .x7 = 0 ∧
      t.c = neg ∧ t.mem = s₁.mem)
      (by
        brun [(k₁.gpr .x12 (by decide)).trans h12, (k₁.gpr .x15 (by decide)).trans h15, cntL]
        exact ⟨BitVec.ofNat_add_ofNat (n := 64) n 1, by cases neg <;> decide⟩) (by decide) (by decide) (by decide +kernel))
    fun s₂ ⟨⟨h14, h7, hc, m₂⟩, k₂⟩ => ?_))
  have k12 := k₁.trans k₂
  refine WP.mono (cnegLoop_ok (hs.congr k12.wr) ((k₂.gpr .x16 (by decide)).trans h16) h14
    ((k12.gpr .x15 (by decide)).trans h15) h7 hc (by omega_arith) (by omega_arith) (by omega_arith)) fun t hI => ⟨?_, ?_, ?_⟩
  · have := hI.val; rw [m₂, m₁] at this; exact this
  · rw [← m₁, ← m₂]; exact hI.out
  · exact (k12.trans hI.keep).mono (by decide)

/-- The sign mask of word `n` as a `mask`. -/
theorem zero_add64' (x y : BitVec 64) : x + 0 + y = x + y := by rw [add_zero64]

theorem signMask_mask (x : BitVec 64) : 0#64 - (x >>> 63) = mask (decide (2 ^ 63 ≤ x.toNat)) := by
  rw [Divstep.signMask_eq]
  by_cases h : x.toNat < 2 ^ 63
  · rw [ite_eq_left h, decide_eq_false (by omega_arith)]; rfl
  · rw [ite_eq_right h, decide_eq_true (by omega_arith)]; rfl

/-- `a + P b` modulo `P Q`, for `a < P`. -/
theorem add_mul_mod_mul {a b P Q : Nat} (ha : a < P) : (a + P * b) % (P * Q) = a + P * (b % Q) := by
  rw [Nat.mod_mul, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.add_mul_div_left _ _ (by omega_arith),
    Nat.div_eq_of_lt ha, Nat.zero_add]

/-- `addIfNeg a m`: `[a] += m` (`n + 1` words, `m` of `n`) if word `n` of `[a]`
is negative, modulo `2^(64 (n + 1))`. -/
theorem addIfNeg_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n)
    (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iA iM : Nat} (hA : iA < 16) (hM : iM < 16)
    (dAM : iA ≠ iM) :
    WP isa (seqs (addIfNeg iA iM)) s fun t =>
      wv t.mem B (slot w iA) (n + 1) = (wv s.mem B (slot w iA) (n + 1) +
        (if 2 ^ 63 ≤ (word s.mem B (slot w iA + 8 * n)).toNat then wv s.mem B (slot w iM) n else 0)) %
          2 ^ (64 * (n + 1)) ∧
      Outside B (slot w iA) (8 * (n + 1)) s.mem t.mem ∧
      Keep [.x3, .x4, .x5, .x7, .x8, .x10, .x14, .x15, .x16] s t ∧ t.v = s.v := by
  have hn' := hs.nowrap
  have sA := Nat.le_trans (slot_lt (w := w) hA) hZ
  have sM := Nat.le_trans (slot_lt (w := w) hM) hZ
  have sepAM := slot_apart (w := w) (a := 8 * n) (b := 8 * n) dAM (by omega_arith) (by omega_arith)
  have bv : ∀ j r, (Code.block (base j r) : Prog isa).allInstrs (fun i => (vdstOf i).isNone) = true := fun j r => by
    simp only [Code.allInstrs_eq, instrs, base_vnone]
  have hvn : (seqs (addIfNeg iA iM)).allInstrs (fun i => (vdstOf i).isNone) = true := by
    simp only [addIfNeg, seqs, signMask, topAt, Code.allInstrs_eq, instrs, List.all_append, base_vnone]; decide
  refine WP.mono (WP.vfix (Q := fun t => wv t.mem B (slot w iA) (n + 1) = (wv s.mem B (slot w iA) (n + 1) +
        (if 2 ^ 63 ≤ (word s.mem B (slot w iA + 8 * n)).toNat then wv s.mem B (slot w iM) n else 0)) %
          2 ^ (64 * (n + 1)) ∧
      Outside B (slot w iA) (8 * (n + 1)) s.mem t.mem ∧
      Keep [.x3, .x4, .x5, .x7, .x8, .x10, .x14, .x15, .x16] s t) ?_ hvn) fun t ⟨⟨a, b, c⟩, v⟩ => ⟨a, b, c, v⟩
  simp only [addIfNeg, seqs, List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (signMask_ok hs iA h0 h11 h12 hn hw hA hZ)
    fun s₁ ⟨⟨h15, h7, m₁, _⟩, k₁⟩ => WP.block_append_iff.mpr (WP.mono (WP.keep [.x3, .x14] (Q := fun t =>
      t.gpr .x14 = BitVec.ofNat 64 n ∧ t.c = false ∧ t.mem = s₁.mem)
      (by brun [(k₁.gpr .x12 (by decide)).trans h12, h7]) (by decide) (by decide) (by decide +kernel))
    fun s₂ ⟨⟨h14, hc, m₂⟩, k₂⟩ => ?_)))
  have k12 := k₁.trans k₂
  refine WP.block_append_iff.mpr (WP.mono (base_ok iM .x10 ((k12.gpr .x0 (by decide)).trans h0)
    ((k12.gpr .x11 (by decide)).trans h11)) fun s₃ ⟨⟨h10, m₃, c₃⟩, k₃⟩ => ?_)
  have k13 := k12.trans k₃
  refine WP.block_append_iff.mpr (WP.mono (base_ok iA .x8 ((k13.gpr .x0 (by decide)).trans h0)
    ((k13.gpr .x11 (by decide)).trans h11)) fun s₄ ⟨⟨h8, m₄, c₄⟩, k₄⟩ => ?_)
  have k14 := k13.trans k₄
  refine WP.mono (base_ok iA .x5 ((k14.gpr .x0 (by decide)).trans h0)
    ((k14.gpr .x11 (by decide)).trans h11)) fun s₅ ⟨⟨h5, m₅, c₅⟩, k₅⟩ => ?_
  have k15 := k14.trans k₅
  have hm₅ : s₅.mem = s.mem := by rw [m₅, m₄, m₃, m₂, m₁]
  refine WP.seq (WP.mono (addMIP_ok (N := n) (c := decide (2 ^ 63 ≤ (word s.mem B (slot w iA + 8 * n)).toNat))
    (hs.congr k15.wr) ((k₅.gpr .x10 (by decide)).trans ((k₄.gpr .x10 (by decide)).trans h10))
    ((k₅.gpr .x8 (by decide)).trans h8) h5
    ((k₅.gpr .x14 (by decide)).trans ((k₄.gpr .x14 (by decide)).trans ((k₃.gpr .x14 (by decide)).trans h14)))
    (by rw [(k₅.gpr .x15 (by decide)).trans ((k₄.gpr .x15 (by decide)).trans ((k₃.gpr .x15 (by decide)).trans
      ((k₂.gpr .x15 (by decide)).trans h15))), signMask_mask])
    (by rw [c₅, c₄, c₃, hc]) hn1 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by rcases sepAM with h | h <;> omega_arith)
    (.inl (Nat.le_refl _))) fun s₆ ⟨e₆, h5', o₆, k₆⟩ => ?_)
  have k16 := k15.trans k₆
  have g7 : s₆.gpr .x7 = 0 := ((((k₂.trans k₃).trans k₄).trans k₅).trans k₆ |>.gpr .x7 (by decide)).trans h7
  have An : wv s₅.mem B (slot w iA) n = wv s.mem B (slot w iA) n := by rw [hm₅]
  have Mn : wv s₅.mem B (slot w iM) n = wv s.mem B (slot w iM) n := by rw [hm₅]
  rw [An, Mn] at e₆
  have top₆ : word s₆.mem B (slot w iA + 8 * n) = word s.mem B (slot w iA + 8 * n) := by
    rw [o₆.word (by omega_arith) (by omega_arith), hm₅]
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s₆.mem.writeW (off B (slot w iA + 8 * n))
      (word s.mem B (slot w iA + 8 * n) + 0 + BitVec.ofNat 64 s₆.c.toNat))
    (by brun [h5', g7, (hs.congr k16.wr).ld (show slot w iA + 8 * n + 8 ≤ Z by omega_arith),
      (hs.congr k16.wr).st (show slot w iA + 8 * n + 8 ≤ Z by omega_arith), top₆]) (by decide) (by decide)
    (by decide +kernel)) fun t ⟨hm, k⟩ => ⟨?_, ?_, (k16.trans k).mono (by decide)⟩
  · rw [hm, wv_writeW_top _ _ _ _ _ (by omega_arith), zero_add64', wv]
    have hW := wv_lt s₆.mem B (slot w iA) n
    have ad : (word s.mem B (slot w iA + 8 * n) + BitVec.ofNat 64 s₆.c.toNat).toNat =
        ((word s.mem B (slot w iA + 8 * n)).toNat + s₆.c.toNat) % 2 ^ 64 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show s₆.c.toNat < 2 ^ 64 by
        have := Bool.toNat_le s₆.c; omega_arith)]
    rw [ad, show 64 * (n + 1) = 64 * n + 64 by omega_arith, Nat.pow_add,
      ← add_mul_mod_mul (Q := 2 ^ 64) hW]
    congr 1
    simp only [decide_eq_true_eq] at e₆
    rw [Nat.mul_add, ← Nat.add_assoc, Nat.add_right_comm, e₆]
    ac_rfl
  · rw [hm, ← hm₅]
    intro x hx
    rw [writeW_outside _ B _ (by omega_arith) x (by omega_arith)]
    exact Outside.mono (o' := slot w iA) (n' := 8 * (n + 1)) o₆ (Nat.le_refl _) (by omega_arith) x hx
/-- `selectAcc`, its output possibly its accumulator. -/
theorem selectAccIP_ok {s : State} {B : Addr} {Z w eA eT eo : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .x8 = off B eA) (h6 : s.gpr .x6 = off B eT) (h5 : s.gpr .x5 = off B eo)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) {lt : Bool} (hc : s.c = !lt)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : eA + 8 * w ≤ Z) (hT : eT + 8 * w ≤ Z) (ho : eo + 8 * w ≤ Z)
    (sA : eo ≤ eA ∨ eA + 8 * w ≤ eo) (sT : eo + 8 * w ≤ eT ∨ eT + 8 * w ≤ eo) :
    WP isa selectAcc s fun t =>
      wv t.mem B eo w = (if lt then wv s.mem B eA w else wv s.mem B eT w) ∧
      Outside B eo (8 * w) s.mem t.mem ∧ Keep [.x3, .x4, .x5, .x6, .x14, .x16] s t := by
  have hn := hs.nowrap
  unfold selectAcc
  refine WP.seq (WP.mono (WP.keep [.x14, .x16] (Q := fun t => t.gpr .x16 = off B eA ∧
    t.gpr .x14 = BitVec.ofNat 64 w ∧ t.c = s.c ∧ t.mem = s.mem) (by brun [h8, h12])
    (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h16, h14, hc₁, hm₁⟩, k₁⟩ => ?_)
  have h0 : SelInv s₁ B Z eA eT eo lt 0 s₁ :=
    ⟨hs.congr k₁.wr, Keep.refl _ _, by rw [h16]; rfl, by rw [k₁.gpr .x6 (by decide), h6]; rfl,
      by rw [k₁.gpr .x5 (by decide), h5]; rfl, hc₁.trans hc, Outside.refl _ _ _ _, by cases lt <;> rfl⟩
  refine WP.mono (wp_countdown (N := w) (by omega_arith) (by omega_arith) (SelInv s₁ B Z eA eT eo lt) ?_ h0 h14)
    fun t hI => ⟨by rw [hI.val, hm₁], by rw [← hm₁]; exact hI.out, (k₁.trans hI.keep).mono (by decide)⟩
  intro j hj t hI _
  have hx : word t.mem B (eA + 8 * j) = word s₁.mem B (eA + 8 * j) := hI.out.word (by omega_arith) (by omega_arith)
  have hy : word t.mem B (eT + 8 * j) = word s₁.mem B (eT + 8 * j) := hI.out.word (by omega_arith) (by omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x6, .x16] (Q := fun t₁ => t₁.mem = t.mem.writeW (off B (eo + 8 * j))
      (if t.c then word t.mem B (eT + 8 * j) else word t.mem B (eA + 8 * j)) ∧ t₁.c = t.c ∧
      t₁.gpr .x16 = off B (eA + 8 * j + 8) ∧ t₁.gpr .x6 = off B (eT + 8 * j + 8) ∧
      t₁.gpr .x5 = off B (eo + 8 * j + 8)) (by
      brun [hI.x16, hI.x6, hI.x5, hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega_arith),
        hI.scr.ld (show eT + 8 * j + 8 ≤ Z by omega_arith), hI.scr.st (show eo + 8 * j + 8 ≤ Z by omega_arith)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, hc', h16', h6', h5'⟩, k₁'⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14', hm', hc''⟩, k'⟩ =>
    ⟨?_, by rw [h14', k₁'.gpr .x14 (by decide)]⟩
  refine ⟨hI.scr.congr (k'.wr.trans k₁'.wr), (hI.keep.trans (k₁'.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16', Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x6 (by decide), h6', Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x5 (by decide), h5', Nat.mul_succ, Nat.add_assoc], by rw [hc'', hc', hI.c], ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega_arith) x (by omega_arith)]
    exact hI.out x (by omega_arith)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega_arith), hI.val, hI.c, hx, hy]
    cases lt <;> simp [wv]


/-- `csubP a m t`: `[a] := [a] mod m` for `[a] < 2 m` (`n + 1` words, `m` of
`n`), through `[t]`, and word `n` of `[a]` cleared. -/
theorem csubP_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n)
    (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iA iM iT : Nat} (hA : iA < 16) (hM : iM < 16)
    (hT : iT < 16) (dAM : iA ≠ iM) (dAT : iA ≠ iT) (dMT : iM ≠ iT) :
    WP isa (seqs (csubP iA iM iT)) s fun t =>
      (wv s.mem B (slot w iA) (n + 1) < 2 * wv s.mem B (slot w iM) n →
        wv t.mem B (slot w iA) (n + 1) = wv s.mem B (slot w iA) (n + 1) % wv s.mem B (slot w iM) n) ∧
      Frm B [(slot w iA, 8 * (n + 1)), (slot w iT, 8 * n)] s.mem t.mem ∧
      Keep [.x3, .x4, .x5, .x6, .x7, .x8, .x10, .x13, .x14, .x16, .x17] s t ∧ t.v = s.v := by
  have hn' := hs.nowrap
  have sA := Nat.le_trans (slot_lt (w := w) hA) hZ
  have sM := Nat.le_trans (slot_lt (w := w) hM) hZ
  have sT := Nat.le_trans (slot_lt (w := w) hT) hZ
  have hvn : (seqs (csubP iA iM iT)).allInstrs (fun i => (vdstOf i).isNone) = true := by
    simp only [csubP, seqs, zeroTop, topAt, selectAcc, Code.allInstrs_eq, instrs, List.all_append,
      base_vnone]; decide
  refine WP.mono (WP.vfix (Q := fun t =>
      (wv s.mem B (slot w iA) (n + 1) < 2 * wv s.mem B (slot w iM) n →
        wv t.mem B (slot w iA) (n + 1) = wv s.mem B (slot w iA) (n + 1) % wv s.mem B (slot w iM) n) ∧
      Frm B [(slot w iA, 8 * (n + 1)), (slot w iT, 8 * n)] s.mem t.mem ∧
      Keep [.x3, .x4, .x5, .x6, .x7, .x8, .x10, .x13, .x14, .x16, .x17] s t) ?_ hvn) fun t ⟨⟨a, b, c⟩, v⟩ => ⟨a, b, c, v⟩
  simp only [csubP, seqs, List.append_assoc]
  have pAT := slot_apart (w := w) (a := 8 * (n + 1)) (b := 8 * n) dAT (by omega_arith) (by omega_arith)
  have pMT := slot_apart (w := w) (a := 8 * n) (b := 8 * n) dMT (by omega_arith) (by omega_arith)
  have pAM := slot_apart (w := w) (a := 8 * (n + 1)) (b := 8 * n) dAM (by omega_arith) (by omega_arith)
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (base_ok iA .x8 h0 h11) fun s₁ ⟨⟨h8, m₁, _⟩, k₁⟩ =>
    WP.block_append_iff.mpr (WP.mono (base_ok iM .x10 ((k₁.gpr .x0 (by decide)).trans h0)
      ((k₁.gpr .x11 (by decide)).trans h11)) fun s₂ ⟨⟨h10, m₂, _⟩, k₂⟩ => ?_)))
  have k12 := k₁.trans k₂
  refine WP.block_append_iff.mpr (WP.mono (base_ok iT .x6 ((k12.gpr .x0 (by decide)).trans h0)
    ((k12.gpr .x11 (by decide)).trans h11)) fun s₃ ⟨⟨h6, m₃, _⟩, k₃⟩ => ?_)
  have k13 := k12.trans k₃
  refine WP.block_append_iff.mpr (WP.mono (base_ok iA .x5 ((k13.gpr .x0 (by decide)).trans h0)
    ((k13.gpr .x11 (by decide)).trans h11)) fun s₄ ⟨⟨h5, m₄, _⟩, k₄⟩ => ?_)
  have k14 := k13.trans k₄
  refine WP.mono (WP.keep [.x7] (Q := fun t => t.gpr .x7 = 0 ∧ t.mem = s₄.mem) (by brun) (by decide) (by decide)
    (by decide +kernel)) fun s₅ ⟨⟨h7, m₅⟩, k₅⟩ => ?_
  have k15 := k14.trans k₅
  have hm₅ : s₅.mem = s.mem := by rw [m₅, m₄, m₃, m₂, m₁]
  refine WP.seq (WP.mono (subMod_ok (w := n) (hs.congr k15.wr)
    ((k₅.gpr .x8 (by decide)).trans ((k₄.gpr .x8 (by decide)).trans ((k₃.gpr .x8 (by decide)).trans
      ((k₂.gpr .x8 (by decide)).trans h8))))
    ((k₅.gpr .x10 (by decide)).trans ((k₄.gpr .x10 (by decide)).trans ((k₃.gpr .x10 (by decide)).trans h10)))
    ((k₅.gpr .x6 (by decide)).trans ((k₄.gpr .x6 (by decide)).trans h6)) ((k15.gpr .x12 (by decide)).trans h12) h7
    hn1 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by rcases pAT with h | h <;> omega_arith)
    (by rcases pMT with h | h <;> omega_arith)) fun s₆ ⟨c, hc, hD, o₆, k₆⟩ => ?_)
  have k16 := k15.trans k₆
  refine WP.seq (WP.mono (selectAccIP_ok (w := n) (hs.congr k16.wr)
    ((k₆.gpr .x8 (by decide)).trans ((k₅.gpr .x8 (by decide)).trans ((k₄.gpr .x8 (by decide)).trans
      ((k₃.gpr .x8 (by decide)).trans ((k₂.gpr .x8 (by decide)).trans h8)))))
    ((k₆.gpr .x6 (by decide)).trans ((k₅.gpr .x6 (by decide)).trans ((k₄.gpr .x6 (by decide)).trans h6)))
    ((k₆.gpr .x5 (by decide)).trans ((k₅.gpr .x5 (by decide)).trans h5)) ((k16.gpr .x12 (by decide)).trans h12)
    hc hn1 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (.inl (Nat.le_refl _)) (by rcases pAT with h | h <;> omega_arith))
    fun s₇ ⟨hv₇, o₇, k₇⟩ => ?_)
  have k17 := k16.trans k₇
  refine WP.mono (zeroTop_ok (hs.congr k17.wr) iA ((k17.gpr .x0 (by decide)).trans h0)
    ((k17.gpr .x11 (by decide)).trans h11) ((k17.gpr .x12 (by decide)).trans h12) hn hw hA hZ)
    fun t ⟨⟨m₈, _, _⟩, k₈⟩ => ⟨fun hlt => ?_, ?_, (k17.trans k₈).mono (by decide)⟩
  · have A6 : wv s₆.mem B (slot w iA) n = wv s.mem B (slot w iA) n := by
      rw [o₆.wv (by rcases pAT with h | h <;> omega_arith) (by omega_arith), hm₅]
    have Aw : word s₆.mem B (slot w iA + 8 * n) = word s.mem B (slot w iA + 8 * n) := by
      rw [o₆.word (by rcases pAT with h | h <;> omega_arith) (by omega_arith), hm₅]
    rw [hm₅] at hD
    have hp := wv_lt s.mem B (slot w iM) n
    have cs := VG.Proof.Bignum.csub_result (Tl := wv s.mem B (slot w iA) n)
      (Tw := (word s.mem B (slot w iA + 8 * n)).toNat) (Tw1 := 0) (D := wv s₆.mem B (slot w iT) n)
      (m := wv s.mem B (slot w iM) n) (R := 2 ^ (64 * n)) (c := c.toNat) hp (wv_lt _ _ _ _) (Bool.toNat_le c)
      (wv_lt _ _ _ _) (by rw [Nat.mul_zero, Nat.add_zero]; rw [wv] at hlt; omega_arith) hD
    rw [hm₅] at hv₇
    rw [m₈, wv_writeW_top _ _ _ _ _ (by omega_arith), hv₇, A6]
    rw [Nat.mul_zero, Nat.add_zero] at cs
    rw [wv, ← cs]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
    by_cases h : (word s.mem B (slot w iA + 8 * n)).toNat < c.toNat <;> simp [h]
  · have f6 : Frm B [(slot w iA, 8 * (n + 1)), (slot w iT, 8 * n)] s₅.mem s₆.mem := Frm.of_outside o₆ (by simp)
    have f7 : Frm B [(slot w iA, 8 * (n + 1)), (slot w iT, 8 * n)] s₆.mem s₇.mem :=
      Frm.of_outside (Outside.mono (o' := slot w iA) (n' := 8 * (n + 1)) o₇ (Nat.le_refl _) (by omega_arith)) (by simp)
    have f8 : Frm B [(slot w iA, 8 * (n + 1)), (slot w iT, 8 * n)] s₇.mem t.mem := by
      rw [m₈]; exact Frm.of_outside (Outside.mono (o' := slot w iA) (n' := 8 * (n + 1))
        (writeW_outside _ B _ (by omega_arith)) (by omega_arith) (by omega_arith)) (by simp)
    rw [← hm₅]; exact (f6.trans f7).trans f8

/-- `dblP a m t s`: `[a] := 2 [a] mod m` (`n` words, `[a] < m`), the double in
`[t]` and the difference in `[s]`. -/
theorem dblP_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n)
    (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iA iM iT iS : Nat} (hA : iA < 16) (hM : iM < 16)
    (hT : iT < 16) (hS : iS < 16) (dAM : iA ≠ iM) (dAT : iA ≠ iT) (dAS : iA ≠ iS) (dMT : iM ≠ iT)
    (dMS : iM ≠ iS) (dTS : iT ≠ iS) :
    WP isa (dblP iA iM iT iS) s fun t =>
      (wv s.mem B (slot w iA) n < wv s.mem B (slot w iM) n →
        wv t.mem B (slot w iA) n = 2 * wv s.mem B (slot w iA) n % wv s.mem B (slot w iM) n) ∧
      Frm B [(slot w iA, 8 * n), (slot w iT, 8 * (n + 1)), (slot w iS, 8 * n)] s.mem t.mem ∧
      Keep [.x3, .x4, .x5, .x6, .x8, .x10, .x13, .x14, .x16, .x17, .x7] s t ∧ t.v = s.v := by
  have hn' := hs.nowrap
  have sl : ∀ j < 16, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_lt (w := w) hj) hZ
  have sA := sl _ hA; have sM := sl _ hM; have sT := sl _ hT; have sS := sl _ hS
  have sp : ∀ {j k}, j ≠ k → slot w j + 8 * (n + 1) ≤ slot w k ∨ slot w k + 8 * (n + 1) ≤ slot w j :=
    fun h => slot_apart (w := w) h (by omega_arith) (by omega_arith)
  have hvn : (dblP iA iM iT iS).allInstrs (fun i => (vdstOf i).isNone) = true := by
    simp only [dblP, selectAcc, countLoop, Code.allInstrs_eq, instrs, List.all_append, base_vnone]; decide
  refine WP.mono (WP.vfix (Q := fun t =>
      (wv s.mem B (slot w iA) n < wv s.mem B (slot w iM) n →
        wv t.mem B (slot w iA) n = 2 * wv s.mem B (slot w iA) n % wv s.mem B (slot w iM) n) ∧
      Frm B [(slot w iA, 8 * n), (slot w iT, 8 * (n + 1)), (slot w iS, 8 * n)] s.mem t.mem ∧
      Keep [.x3, .x4, .x5, .x6, .x8, .x10, .x13, .x14, .x16, .x17, .x7] s t) ?_ hvn) fun t ⟨⟨a, b, c⟩, v⟩ => ⟨a, b, c, v⟩
  unfold dblP
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (base_ok iA .x5 h0 h11) fun s₁ ⟨⟨h5, m₁, _⟩, k₁⟩ =>
    WP.block_append_iff.mpr (WP.mono (base_ok iM .x10 ((k₁.gpr .x0 (by decide)).trans h0)
      ((k₁.gpr .x11 (by decide)).trans h11)) fun s₂ ⟨⟨h10, m₂, _⟩, k₂⟩ => ?_)))
  have k12 := k₁.trans k₂
  refine WP.block_append_iff.mpr (WP.mono (base_ok iT .x8 ((k12.gpr .x0 (by decide)).trans h0)
    ((k12.gpr .x11 (by decide)).trans h11)) fun s₃ ⟨⟨h8, m₃, _⟩, k₃⟩ => ?_)
  have k13 := k12.trans k₃
  refine WP.block_append_iff.mpr (WP.mono (base_ok iS .x6 ((k13.gpr .x0 (by decide)).trans h0)
    ((k13.gpr .x11 (by decide)).trans h11)) fun s₄ ⟨⟨h6, m₄, _⟩, k₄⟩ => ?_)
  have k14 := k13.trans k₄
  refine WP.mono (WP.keep [.x7, .x14, .x16, .x17, .x3] (Q := fun t => t.gpr .x7 = 0 ∧
      t.gpr .x17 = off B (slot w iA) ∧ t.gpr .x16 = off B (slot w iT) ∧ t.gpr .x14 = BitVec.ofNat 64 n ∧
      t.c = false ∧ t.mem = s₄.mem)
    (by brun [(k₄.gpr .x5 (by decide)).trans ((k₃.gpr .x5 (by decide)).trans ((k₂.gpr .x5 (by decide)).trans h5)),
      (k₄.gpr .x8 (by decide)).trans h8, (k14.gpr .x12 (by decide)).trans h12])
    (by decide) (by decide) (by decide +kernel)) fun s₅ ⟨⟨h7, h17, h16, h14, hc₅, m₅⟩, k₅⟩ => ?_
  have k15 := k14.trans k₅
  have hm₅ : s₅.mem = s.mem := by rw [m₅, m₄, m₃, m₂, m₁]
  have e5 : s₅.gpr .x5 = off B (slot w iA) :=
    (k₅.gpr .x5 (by decide)).trans ((k₄.gpr .x5 (by decide)).trans ((k₃.gpr .x5 (by decide)).trans
      ((k₂.gpr .x5 (by decide)).trans h5)))
  have e10 : s₅.gpr .x10 = off B (slot w iM) :=
    (k₅.gpr .x10 (by decide)).trans ((k₄.gpr .x10 (by decide)).trans ((k₃.gpr .x10 (by decide)).trans h10))
  have e8 : s₅.gpr .x8 = off B (slot w iT) := (k₅.gpr .x8 (by decide)).trans ((k₄.gpr .x8 (by decide)).trans h8)
  have e6 : s₅.gpr .x6 = off B (slot w iS) := (k₅.gpr .x6 (by decide)).trans h6
  have e12 : s₅.gpr .x12 = BitVec.ofNat 64 n := (k15.gpr .x12 (by decide)).trans h12
  have pTA := sp (Ne.symm dAT); have pTS := sp dTS; have pMS := sp dMS; have pAS := sp dAS
  have pAM := sp dAM; have pMT := sp dMT
  have hs₅ := hs.congr k15.wr
  have h0' : DblInv s₅ B Z (slot w iT) (slot w iA) 0 s₅ :=
    ⟨hs₅, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, Outside.refl _ _ _ _, by rw [hc₅]; rfl⟩
  refine WP.seq (WP.mono (wp_countdown (N := n) (by omega_arith) (by omega_arith)
    (DblInv s₅ B Z (slot w iT) (slot w iA))
    (fun j hj t hI _ => dblStep_ok (w := n) (by omega_arith) (by omega_arith)
      (by rcases pTA with h | h <;> omega_arith) hj hI) h0' h14) fun s₆ hI => ?_)
  have hval := hI.val
  have s₆7 : s₆.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans h7
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun t =>
      t.mem = s₆.mem.writeW (off B (slot w iT + 8 * n)) (BitVec.ofNat 64 s₆.c.toNat))
    (by brun [hI.x16, s₆7, hI.scr.st (show slot w iT + 8 * n + 8 ≤ Z by omega_arith)]
        simp only [add_zero64, zero_add64])
    (by decide) (by decide) (by decide +kernel)) fun s₇ ⟨hm₇, k₇⟩ => ?_)
  have hs₇ := hI.scr.congr k₇.wr
  have k57 := hI.keep.trans k₇
  have o7 : Outside B (slot w iT) (8 * (n + 1)) s₅.mem s₇.mem := by
    rw [hm₇]
    intro x hx
    rw [writeW_outside s₆.mem B _ (by omega_arith) x (by omega_arith)]
    exact hI.out x (by omega_arith)
  rw [hm₅] at o7
  have fM : wv s₇.mem B (slot w iM) n = wv s.mem B (slot w iM) n :=
    o7.wv (by rcases pMT with h | h <;> omega_arith) (by omega_arith)
  have hTl : wv s₇.mem B (slot w iT) n = wv s₆.mem B (slot w iT) n := by
    rw [hm₇]; exact (writeW_outside s₆.mem B _ (by omega_arith)).wv (Or.inl (by omega_arith)) (by omega_arith)
  have hTw : (word s₇.mem B (slot w iT + 8 * n)).toNat = s₆.c.toNat := by
    rw [hm₇, word_writeW_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Bool.toNat_le s₆.c; omega_arith)]
  refine WP.seq (WP.mono (subMod_ok (w := n) hs₇ ((k57.gpr .x8 (by decide)).trans e8)
    ((k57.gpr .x10 (by decide)).trans e10) ((k57.gpr .x6 (by decide)).trans e6)
    ((k57.gpr .x12 (by decide)).trans e12) ((k57.gpr .x7 (by decide)).trans h7) hn1 (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by rcases pTS with h | h <;> omega_arith) (by rcases pMS with h | h <;> omega_arith))
    fun s₈ ⟨c', hc₈, hD, o₈, k₈⟩ => ?_)
  have k58 := k57.trans k₈
  refine WP.mono (selectAcc_ok (w := n) (hs₇.congr k₈.wr) ((k58.gpr .x8 (by decide)).trans e8)
    ((k58.gpr .x6 (by decide)).trans e6) ((k58.gpr .x5 (by decide)).trans e5)
    ((k58.gpr .x12 (by decide)).trans e12) hc₈ hn1 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by rcases pTA with h | h <;> omega_arith) (by rcases pAS with h | h <;> omega_arith)) fun t ⟨hv', hot, k₉⟩ => ?_
  have hT₈ : wv s₈.mem B (slot w iT) n = wv s₇.mem B (slot w iT) n :=
    o₈.wv (by rcases pTS with h | h <;> omega_arith) (by omega_arith)
  rw [fM] at hD
  have fA : wv s₅.mem B (slot w iA) n = wv s.mem B (slot w iA) n := by rw [hm₅]
  rw [fA] at hval
  refine ⟨fun hlt => ?_, ?_, ((k15.trans k58).trans k₉).mono (by decide)⟩
  · rw [hv', hT₈, hTw]
    have := VG.Proof.Bignum.csub_result (Tl := wv s₇.mem B (slot w iT) n) (Tw := s₆.c.toNat) (Tw1 := 0)
      (D := wv s₈.mem B (slot w iS) n) (m := wv s.mem B (slot w iM) n) (R := 2 ^ (64 * n))
      (c := c'.toNat) (wv_lt s.mem B (slot w iM) n) (wv_lt _ _ _ _) (Bool.toNat_le c')
      (wv_lt _ _ _ _) (by rw [hTl, Nat.mul_zero, Nat.add_zero]; omega_arith) hD
    rw [Nat.mul_zero, Nat.add_zero, hTl, hval] at this
    rw [← this]
    by_cases h : s₆.c.toNat < c'.toNat <;> simp [h, hTl]
  · have f7 : Frm B [(slot w iA, 8 * n), (slot w iT, 8 * (n + 1)), (slot w iS, 8 * n)] s.mem s₇.mem :=
      Frm.of_outside o7 (by simp)
    have f8 : Frm B [(slot w iA, 8 * n), (slot w iT, 8 * (n + 1)), (slot w iS, 8 * n)] s₇.mem s₈.mem :=
      Frm.of_outside o₈ (by simp)
    have f9 : Frm B [(slot w iA, 8 * n), (slot w iT, 8 * (n + 1)), (slot w iS, 8 * n)] s₈.mem t.mem :=
      Frm.of_outside hot (by simp)
    exact (f7.trans f8).trans f9
end VG.Proof.Rsa.AArch64

-- From `Proof/Rsa/AArch64/InvFinish.lean`.
/-!
# RSA private keys on AArch64: the end of the batched inverse

After the batches (`LInv` after `3 n + 2` of them), `batchFinish`: `f` and
`a` negated if `f < 0` (`|f| = gcd(p, x)`), `p` added twice to `a` if
negative and `a mod p` (now in `[0, 2p)`), then `15 n + 10` modular
doublings (`dblLoop_ok`), the `2^5` each batch's Montgomery reductions took
off, and `x1`, `x2` restored (`finish_ok`; `Rsa.Divstep.invRunS59_result`
for the result).
-/


namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.InvBatch
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Divstep (sgn)

/-- The doublings' registers. -/
abbrev dblRegs : List Reg := [.x3, .x4, .x5, .x6, .x8, .x10, .x13, .x14, .x16, .x17, .x7, .x15]

/-- After `j` doublings from `s₀`. -/
structure DInv (s₀ : State) (B : Addr) (Z w n iA iM iT iS : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  x0 : t.gpr .x0 = B
  x11 : t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))
  x12 : t.gpr .x12 = BitVec.ofNat 64 n
  val : wv s₀.mem B (slot w iA) n < wv s₀.mem B (slot w iM) n →
    wv t.mem B (slot w iA) n = wv s₀.mem B (slot w iA) n * 2 ^ j % wv s₀.mem B (slot w iM) n
  frm : Frm B [(slot w iA, 8 * n), (slot w iT, 8 * (n + 1)), (slot w iS, 8 * n)] s₀.mem t.mem
  keep : Keep dblRegs s₀ t
  v : t.v = s₀.v

/-- `K` modular doublings of `[a]` (`n` words, below `m`), counted by `x15`. -/
theorem dblLoop_ok {s : State} {B : Addr} {Z w n K : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n)
    (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iA iM iT iS : Nat} (hA : iA < 16) (hM : iM < 16)
    (hT : iT < 16) (hS : iS < 16) (dAM : iA ≠ iM) (dAT : iA ≠ iT) (dAS : iA ≠ iS) (dMT : iM ≠ iT)
    (dMS : iM ≠ iS) (dTS : iT ≠ iS) (hK : 0 < K) (hK' : K < 2 ^ 64) (h15 : s.gpr .x15 = BitVec.ofNat 64 K) :
    WP isa (.loop (.seq (dblP iA iM iT iS) (.block [.subImm .x .x15 .x15 1])) (.nonzero .x .x15)) s
      (DInv s B Z w n iA iM iT iS K) := by
  have hn' := hs.nowrap
  have sM := Nat.le_trans (slot_lt (w := w) hM) hZ
  have apM : ∀ r ∈ [(slot w iA, 8 * n), (slot w iT, 8 * (n + 1)), (slot w iS, 8 * n)],
      slot w iM + 8 * n ≤ r.1 ∨ r.1 + r.2 ≤ slot w iM := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact slot_apart (w := w) dAM.symm (by omega_arith) (by omega_arith)
    · exact slot_apart (w := w) dMT (by omega_arith) (by omega_arith)
    · exact slot_apart (w := w) dMS (by omega_arith) (by omega_arith)
  refine wp_countdown (N := K) hK' hK (DInv s B Z w n iA iM iT iS) (fun j _ t hI _ => ?_)
    ⟨hs, h0, h11, h12, fun h => by rw [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt h], Frm.refl _ _ _,
      Keep.refl _ _, rfl⟩ h15
  have fM : wv t.mem B (slot w iM) n = wv s.mem B (slot w iM) n := hI.frm.wv_eq apM (by omega_arith)
  refine WP.seq (WP.mono (dblP_ok hI.scr hI.x0 hI.x11 hI.x12 hn1 hn hw hZ hA hM hT hS dAM dAT dAS dMT dMS dTS)
    fun t₁ ⟨v₁, f₁, k₁, vv₁⟩ => WP.mono (WP.vfix (dec_ok t₁ .x15) (by decide)) fun t' ⟨⟨⟨c', m', _⟩, k'⟩, vv'⟩ =>
      ⟨?_, ?_⟩)
  · have k1' := k₁.trans k'
    refine ⟨hI.scr.congr k1'.wr, (k1'.gpr .x0 (by decide)).trans hI.x0, (k1'.gpr .x11 (by decide)).trans hI.x11,
      (k1'.gpr .x12 (by decide)).trans hI.x12, fun h => ?_, ?_, (hI.keep.trans k1').mono (by decide), ?_⟩
    · have hv := hI.val h
      have hlt : wv t.mem B (slot w iA) n < wv t.mem B (slot w iM) n := by
        rw [hv, fM]; exact Nat.mod_lt _ (by omega_arith)
      rw [m', v₁ hlt, hv, fM, Nat.mul_mod_mod, Nat.pow_succ]; congr 1; ac_rfl
    · rw [← m'] at f₁; exact hI.frm.trans f₁
    · rw [vv', vv₁, hI.v]
  · rw [c', k₁.gpr .x15 (by decide)]


/-- `addIfNeg`'s step on signed numbers: the top word's top bit is the sign. -/
theorem addIfNeg_step {n X Y W top p : Nat} (hX : X = W + 2 ^ (64 * n) * top) (hW : W < 2 ^ (64 * n))
    (htop : top < 2 ^ 64) (hY : Y = (X + if 2 ^ 63 ≤ top then p else 0) % 2 ^ (64 * (n + 1)))
    (r₀ : -2 ^ (64 * (n + 1) - 1) ≤ sgn (n + 1) X + if sgn (n + 1) X < 0 then (p : Int) else 0)
    (r₁ : sgn (n + 1) X + (if sgn (n + 1) X < 0 then (p : Int) else 0) < 2 ^ (64 * (n + 1) - 1)) :
    sgn (n + 1) Y = sgn (n + 1) X + if sgn (n + 1) X < 0 then (p : Int) else 0 := by
  have hiff := Divstep.sgn_neg_iff hW htop
  rw [← hX] at hiff
  have hXR : X < 2 ^ (64 * (n + 1)) := by
    have : 2 ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by
      rw [← Nat.pow_add, show 64 * n + 64 = 64 * (n + 1) by omega_arith]
    have := Nat.mul_le_mul_left (2 ^ (64 * n)) (show top + 1 ≤ 2 ^ 64 by omega_arith)
    rw [Nat.mul_add, Nat.mul_one] at this
    omega_arith
  refine Divstep.sgn_addIfNeg (by omega_arith) hXR ?_ r₀ r₁
  rw [hY]
  by_cases h : sgn (n + 1) X < 0
  · rw [ite_eq_left (hiff.mp h), ite_eq_left h]; push_cast; rfl
  · rw [ite_eq_right (fun h' => h (hiff.mpr h')), ite_eq_right h]; push_cast; rfl

/-- A number of `n + 1` words whose signed value is below `2^(64 n)` and not
negative: that value, and its top word zero. -/
theorem small_of_sgn {n X W top : Nat} {v : Int} (hX : X = W + 2 ^ (64 * n) * top) (hW : W < 2 ^ (64 * n))
    (htop : top < 2 ^ 64) (h : sgn (n + 1) X = v) (h0 : 0 ≤ v) (h1 : v < 2 ^ (64 * n)) :
    (X : Int) = v ∧ (W : Int) = v := by
  have hiff := Divstep.sgn_neg_iff hW htop
  rw [← hX, h] at hiff
  have ht : top < 2 ^ 63 := Nat.lt_of_not_le fun h' => absurd (hiff.mpr h') (by omega_arith)
  have := Divstep.top_sign hW htop
  rw [← hX] at this
  have hx : X < 2 ^ (64 * (n + 1) - 1) := this.mpr ht
  unfold sgn at h
  rw [ite_eq_left hx] at h
  refine ⟨h, ?_⟩
  have : top = 0 := by
    rcases Nat.eq_zero_or_pos top with h' | h'
    · exact h'
    · have := Nat.mul_le_mul_left (2 ^ (64 * n)) h'
      have : (X : Int) < 2 ^ (64 * n) := by rw [h]; exact h1
      have : X < 2 ^ (64 * n) := by exact_mod_cast this
      omega_arith
  subst this
  rw [hX, Nat.mul_zero, Nat.add_zero] at h
  exact h

/-- The end of the batched inverse, after the `3 n + 2` batches: for a good
`p`, `[v] = gcd(p, a)` and `[x₂] a ≡ gcd(p, a) (mod p)`, `[x₂] < p`. -/
theorem finish_ok {C : ICfg} (hC : C.Ok) {s₀ s : State} (hI : LInv C s₀ (3 * C.n + 2) s) :
    WP isa (seqs (batchFinish C.iV C.iU C.iX₂ C.iM C.iT)) s fun t =>
      Scr t C.B C.Z ∧ t.gpr .x0 = C.B ∧ t.gpr .x1 = s₀.gpr .x1 ∧ t.gpr .x2 = s₀.gpr .x2 ∧
      t.gpr .x11 = BitVec.ofNat 64 (8 * (C.w + 2)) ∧ t.gpr .x12 = BitVec.ofNat 64 C.n ∧
      Frm C.B C.ranges s₀.mem t.mem ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s₀ t ∧
      (C.Good → ∀ a, a < 2 ^ (64 * C.n) → C.x = Rsa.Divstep.oddInput C.p a →
        wv t.mem C.B (slot C.w C.iV) C.n = Nat.gcd C.p a ∧
        (C.p : Int) ∣ (wv t.mem C.B (slot C.w C.iX₂) C.n : Int) * a - Nat.gcd C.p a ∧
        wv t.mem C.B (slot C.w C.iX₂) C.n < C.p) := by
  have hn' := hI.scr.nowrap
  have hn1 := hC.n1; have hnw := hC.nw; have hw := hC.w24; have hZ := hC.hZ
  have hZ' : slot C.w 16 + C.B.toNat ≤ 2 ^ 64 := by omega_arith
  have sl : ∀ j < 16, slot C.w j + 8 * (C.w + 2) ≤ C.Z := fun j hj => Nat.le_trans (slot_lt (w := C.w) hj) hZ
  have sV := sl _ hC.hV; have sX₂ := sl _ hC.hX₂; have sM := sl _ hC.hM
  have rg : ∀ {j : Nat} {len : Nat}, (slot C.w j, 8 * (C.w + 2)) ∈ C.ranges → len ≤ 8 * (C.w + 2) →
      ∀ {m m' : Mem}, Outside C.B (slot C.w j) len m m' → Frm C.B C.ranges m m' := fun {j len} hr hl {m m'} o =>
    Frm.of_outside (Outside.mono (o' := slot C.w j) (n' := 8 * (C.w + 2)) o (Nat.le_refl _) (by omega_arith)) hr
  have rV : (slot C.w C.iV, 8 * (C.w + 2)) ∈ C.ranges := by simp [ICfg.ranges]
  have rX₂ : (slot C.w C.iX₂, 8 * (C.w + 2)) ∈ C.ranges := by simp [ICfg.ranges]
  have rT : (slot C.w C.iT, 8 * (C.w + 2)) ∈ C.ranges := by simp [ICfg.ranges]
  have rU : (slot C.w C.iU, 8 * (C.w + 2)) ∈ C.ranges := by simp [ICfg.ranges]
  unfold batchFinish
  rw [show ([Code.block (signMask C.iV), cnegP C.iV, cnegP C.iX₂] ++ addIfNeg C.iX₂ C.iM ++ addIfNeg C.iX₂ C.iM ++
      csubP C.iX₂ C.iM C.iT ++ [.seq (.block dblCount) (.loop (.seq (dblP C.iX₂ C.iM C.iT C.iU)
        (.block [.subImm .x .x15 .x15 1])) (.nonzero .x .x15)), .block [.umov .x .x1 .v19 0, .umov .x .x2 .v19 1,
      .vop (.movi0 .v16), .vop (.movi0 .v17), .vop (.movi0 .v18), .vop (.movi0 .v19), .vop (.movi0 .v20), .vop (.movi0 .v21), .vop (.movi0 .v22), .vop (.movi0 .v23), .vop (.movi0 .v24), .vop (.movi0 .v25), .vop (.movi0 .v26)]] :
      List (Prog isa)) = [Code.block (signMask C.iV), cnegP C.iV, cnegP C.iX₂] ++ (addIfNeg C.iX₂ C.iM ++
      (addIfNeg C.iX₂ C.iM ++ (csubP C.iX₂ C.iM C.iT ++ [.seq (.block dblCount) (.loop (.seq (dblP C.iX₂ C.iM C.iT C.iU)
        (.block [.subImm .x .x15 .x15 1])) (.nonzero .x .x15)), .block [.umov .x .x1 .v19 0, .umov .x .x2 .v19 1,
      .vop (.movi0 .v16), .vop (.movi0 .v17), .vop (.movi0 .v18), .vop (.movi0 .v19), .vop (.movi0 .v20), .vop (.movi0 .v21), .vop (.movi0 .v22), .vop (.movi0 .v23), .vop (.movi0 .v24), .vop (.movi0 .v25), .vop (.movi0 .v26)]])))
      by simp only [List.append_assoc]]
  refine wp_seqs_append (by simp) (by simp [addIfNeg]) ?_
  simp only [seqs]
  -- The sign of `f` into `x15`.
  refine WP.seq (WP.mono (signMask_ok hI.scr C.iV hI.x0 hI.x11 hI.x12 hnw hw hC.hV hZ)
    fun s₁ ⟨⟨h15, h7, m₁, v₁⟩, k₁⟩ => ?_)
  rw [signMask_mask] at h15
  have k01 := k₁
  -- `f := |f|`, `a := ±a`.
  refine WP.seq (WP.mono (cnegP_ok (hI.scr.congr k₁.wr) ((k₁.gpr .x0 (by decide)).trans hI.x0)
    ((k₁.gpr .x11 (by decide)).trans hI.x11) ((k₁.gpr .x12 (by decide)).trans hI.x12) hnw hw hZ hC.hV h15)
    fun s₂ ⟨e₂, o₂, k₂, v₂⟩ => ?_)
  have k02 := k01.trans k₂
  refine WP.mono (cnegP_ok (hI.scr.congr (k₁.trans k₂).wr) ((k02.gpr .x0 (by decide)).trans hI.x0)
    ((k02.gpr .x11 (by decide)).trans hI.x11) ((k02.gpr .x12 (by decide)).trans hI.x12) hnw hw hZ hC.hX₂
    ((k₂.gpr .x15 (by decide)).trans h15)) fun s₃ ⟨e₃, o₃, k₃, v₃⟩ => ?_
  have k03 := k02.trans k₃
  have sc₃ : Scr s₃ C.B C.Z := hI.scr.congr ((k₁.trans k₂).trans k₃).wr
  -- `p` added to `a` twice if negative.
  refine wp_seqs_append (by simp [addIfNeg]) (by simp [addIfNeg]) (WP.mono (addIfNeg_ok sc₃
    ((k03.gpr .x0 (by decide)).trans hI.x0) ((k03.gpr .x11 (by decide)).trans hI.x11)
    ((k03.gpr .x12 (by decide)).trans hI.x12) hn1 hnw hw hZ hC.hX₂ hC.hM hC.dX₂M) fun s₄ ⟨e₄, o₄, k₄, v₄⟩ => ?_)
  have k04 := k03.trans k₄
  have sc₄ : Scr s₄ C.B C.Z := sc₃.congr k₄.wr
  refine wp_seqs_append (by simp [addIfNeg]) (by simp [csubP]) (WP.mono (addIfNeg_ok sc₄
    ((k04.gpr .x0 (by decide)).trans hI.x0) ((k04.gpr .x11 (by decide)).trans hI.x11)
    ((k04.gpr .x12 (by decide)).trans hI.x12) hn1 hnw hw hZ hC.hX₂ hC.hM hC.dX₂M) fun s₅ ⟨e₅, o₅, k₅, v₅⟩ => ?_)
  have k05 := k04.trans k₅
  have sc₅ : Scr s₅ C.B C.Z := sc₄.congr k₅.wr
  -- `a mod p`.
  refine wp_seqs_append (by simp [csubP]) (by simp) (WP.mono (csubP_ok sc₅
    ((k05.gpr .x0 (by decide)).trans hI.x0) ((k05.gpr .x11 (by decide)).trans hI.x11)
    ((k05.gpr .x12 (by decide)).trans hI.x12) hn1 hnw hw hZ hC.hX₂ hC.hM hC.hT hC.dX₂M hC.dX₂T hC.dMT)
    fun s₆ ⟨e₆, f₆, k₆, v₆⟩ => ?_)
  have k06 := k05.trans k₆
  have sc₆ : Scr s₆ C.B C.Z := sc₅.congr k₆.wr
  simp only [seqs]
  -- The doublings.
  refine WP.seq (WP.seq (WP.mono (WP.vfix (WP.keep [.x15] (Q := fun t =>
      t.gpr .x15 = BitVec.ofNat 64 (15 * C.n + 10) ∧ t.mem = s₆.mem)
      (by
        unfold dblCount
        brun [(k06.gpr .x12 (by decide)).trans hI.x12, shl_ofNat (show C.n * 2 ^ 4 < 2 ^ 64 by omega_arith)]
        apply BitVec.eq_of_toNat_eq
        have := hC.n21
        simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega_arith)
      (by decide) (by decide) (by decide +kernel)) (by decide +kernel))
    fun s₇ ⟨⟨⟨h15₇, m₇⟩, k₇⟩, v₇⟩ => WP.mono (dblLoop_ok (K := 15 * C.n + 10) (sc₆.congr k₇.wr)
      ((k₇.gpr .x0 (by decide)).trans ((k06.gpr .x0 (by decide)).trans hI.x0))
      ((k₇.gpr .x11 (by decide)).trans ((k06.gpr .x11 (by decide)).trans hI.x11))
      ((k₇.gpr .x12 (by decide)).trans ((k06.gpr .x12 (by decide)).trans hI.x12)) hn1 hnw hw hZ hC.hX₂ hC.hM hC.hT
      hC.hU hC.dX₂M hC.dX₂T hC.dUX₂.symm hC.dMT hC.dUM.symm hC.dUT.symm (by omega_arith) (by omega_arith) h15₇)
    fun s₈ hD => ?_))
  have k07 := k06.trans k₇
  have k08 := k07.trans hD.keep
  -- `x1`, `x2` back.
  refine WP.mono (WP.keep [.x1, .x2] (Q := fun t => t.gpr .x1 = (s₈.v .v19).extractLsb' 0 64 ∧
      t.gpr .x2 = (s₈.v .v19).extractLsb' 64 64 ∧ t.mem = s₈.mem)
    (by brun [exec_umov_x, exec_movi0, RegUpd.v_write, RegUpd.gpr_setV, RegUpd.mem_setV, Nat.mul_zero,
      Nat.mul_one]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨t1, t2, mt⟩, kt⟩ => ?_
  have k0t := hI.keep.trans (k08.trans kt)
  have vv : s₈.v = s.v := by rw [hD.v, v₇, v₆, v₅, v₄, v₃, v₂, v₁]
  refine ⟨hD.scr.congr kt.wr, (kt.gpr .x0 (by decide)).trans hD.x0, ?_, ?_, (kt.gpr .x11 (by decide)).trans hD.x11,
    (kt.gpr .x12 (by decide)).trans hD.x12, ?_, k0t.mono (by decide), ?_⟩
  · rw [t1, vv]; exact hI.x1s
  · rw [t2, vv]; exact hI.x2s
  · have w6 : Frm C.B C.ranges s₅.mem s₆.mem := Frm.widen f₆ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, rX₂, Nat.le_refl _, by dsimp only; omega_arith⟩
      · exact ⟨_, rT, Nat.le_refl _, by dsimp only; omega_arith⟩
    have w8 : Frm C.B C.ranges s₇.mem s₈.mem := Frm.widen hD.frm fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, rX₂, Nat.le_refl _, by dsimp only; omega_arith⟩
      · exact ⟨_, rT, Nat.le_refl _, by dsimp only; omega_arith⟩
      · exact ⟨_, rU, Nat.le_refl _, by dsimp only; omega_arith⟩
    rw [mt]
    refine hI.frm.trans ?_
    rw [m₁] at o₂
    rw [m₇] at w8
    exact (((((rg rV (by omega_arith) o₂).trans (rg rX₂ (by omega_arith) o₃)).trans (rg rX₂ (by omega_arith) o₄)).trans
      (rg rX₂ (by omega_arith) o₅)).trans w6).trans w8
  · intro G a ha hx
    have hL : 1 ≤ C.n + 1 := by omega_arith
    have hpf : C.pf = C.p := by unfold ICfg.pf; have := G.1; omega_arith
    have hm' : ((C.p : Int) * C.mi.toNat + 1) % 2 ^ 64 = 0 := by
      have := hC.hm; rw [show C.p + (1 - C.p % 2) = C.p by have := G.1; omega_arith] at this; exact this
    have hp1 : (1 : Int) < C.p := by exact_mod_cast G.2
    have est : C.st (3 * C.n + 2) =
        Divstep.invRunS 59 C.p C.mi.toNat (Rsa.Divstep.oddInput C.p a) (3 * C.n + 2) := by
      unfold ICfg.st; rw [hpf, hx]
    obtain ⟨-, rf0, rr⟩ := Rsa.Divstep.invRunS59_result (mi := C.mi.toNat) G.1 hm' hC.pC ha
    obtain ⟨ra0, ra1, -, -⟩ := Divstep.invRunS_range (N := 59) (p := C.p) (m := C.mi.toNat)
      (x := Rsa.Divstep.oddInput C.p a) (by decide) hp1 hm' (3 * C.n + 2)
    rw [← est] at rf0 rr ra0 ra1
    have hf := hI.f
    have hav := hI.a G
    set f := (C.st (3 * C.n + 2)).f with hfdef
    set av := (C.st (3 * C.n + 2)).a with hadef
    have gp : Nat.gcd C.p a ≤ C.p := Nat.gcd_le_left _ (by omega_arith)
    have pC := hC.pC
    have half : (2 : Int) ^ (64 * C.n) * 2 ≤ 2 ^ (64 * (C.n + 1) - 1) := by
      have : 2 ^ (64 * C.n) * 2 ≤ 2 ^ (64 * (C.n + 1) - 1) := by
        rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) (by omega_arith)
      exact_mod_cast this
    have pC' : (C.p : Int) < 2 ^ (64 * C.n) := by exact_mod_cast pC
    have fabs : |f| = (Nat.gcd C.p a : Int) := by rw [← Int.natCast_natAbs, rf0]
    have fabs' : |f| < 2 ^ (64 * C.n) := by rw [fabs]; omega_arith
    -- Memory between the stages.
    have M₀ := hI.m
    have wsucc : ∀ (m : Mem) (j : Nat), wv m C.B (slot C.w j) (C.n + 1) =
        wv m C.B (slot C.w j) C.n + 2 ^ (64 * C.n) * (word m C.B (slot C.w j + 8 * C.n)).toNat := fun m j => by
      rw [wv]
    have M₃ : wv s₃.mem C.B (slot C.w C.iM) C.n = C.p := by
      rw [wv_out o₃ hC.dX₂M (by omega_arith) (by omega_arith) hZ' hC.hM, wv_out o₂ hC.dVM (by omega_arith) (by omega_arith) hZ' hC.hM, m₁, M₀]
    have M₄ : wv s₄.mem C.B (slot C.w C.iM) C.n = C.p := by
      rw [wv_out o₄ hC.dX₂M (by omega_arith) (by omega_arith) hZ' hC.hM, M₃]
    have M₅ : wv s₅.mem C.B (slot C.w C.iM) C.n = C.p := by
      rw [wv_out o₅ hC.dX₂M (by omega_arith) (by omega_arith) hZ' hC.hM, M₄]
    have apM6 : ∀ r ∈ [(slot C.w C.iX₂, 8 * (C.n + 1)), (slot C.w C.iT, 8 * C.n)],
        slot C.w C.iM + 8 * C.n ≤ r.1 ∨ r.1 + r.2 ≤ slot C.w C.iM := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slot_apart (w := C.w) hC.dX₂M.symm (by omega_arith) (by omega_arith)
      · exact slot_apart (w := C.w) hC.dMT (by omega_arith) (by omega_arith)
    have M₇ : wv s₇.mem C.B (slot C.w C.iM) C.n = C.p := by
      rw [m₇, f₆.wv_eq apM6 (by omega_arith), M₅]
    -- `|f|` in `v`.
    have hneg : (2 ^ 63 ≤ (word s.mem C.B (slot C.w C.iV + 8 * C.n)).toNat) ↔ f < 0 := by
      rw [← hf, wsucc]
      exact (Divstep.sgn_neg_iff (wv_lt _ _ _ _) (BitVec.isLt _)).symm
    rw [m₁] at e₂
    have V₂ := Divstep.sgn_cneg hL (wv_lt _ _ _ _) (wv_lt _ _ _ _) (by rw [hf]; omega_arith) e₂
    rw [hf] at V₂
    have V₂' : sgn (C.n + 1) (wv s₂.mem C.B (slot C.w C.iV) (C.n + 1)) = |f| := by
      rw [V₂]
      by_cases h : f < 0
      · rw [ite_eq_left (decide_eq_true (hneg.mpr h)), abs_of_neg h]
      · rw [ite_eq_right (by simp only [decide_eq_true_eq]; exact fun h' => h (hneg.mp h')), abs_of_nonneg (by omega_arith)]
    obtain ⟨-, V₂n⟩ := small_of_sgn (wsucc _ _) (wv_lt _ _ _ _) (BitVec.isLt _) V₂' (abs_nonneg _) fabs'
    have apV6 : ∀ r ∈ [(slot C.w C.iX₂, 8 * (C.n + 1)), (slot C.w C.iT, 8 * C.n)],
        slot C.w C.iV + 8 * C.n ≤ r.1 ∨ r.1 + r.2 ≤ slot C.w C.iV := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slot_apart (w := C.w) hC.dVX₂ (by omega_arith) (by omega_arith)
      · exact slot_apart (w := C.w) hC.dVT (by omega_arith) (by omega_arith)
    have apV8 : ∀ r ∈ [(slot C.w C.iX₂, 8 * C.n), (slot C.w C.iT, 8 * (C.n + 1)), (slot C.w C.iU, 8 * C.n)],
        slot C.w C.iV + 8 * C.n ≤ r.1 ∨ r.1 + r.2 ≤ slot C.w C.iV := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact slot_apart (w := C.w) hC.dVX₂ (by omega_arith) (by omega_arith)
      · exact slot_apart (w := C.w) hC.dVT (by omega_arith) (by omega_arith)
      · exact slot_apart (w := C.w) hC.dUV.symm (by omega_arith) (by omega_arith)
    have Vt : wv t.mem C.B (slot C.w C.iV) C.n = Nat.gcd C.p a := by
      rw [mt, hD.frm.wv_eq apV8 (by omega_arith), m₇, f₆.wv_eq apV6 (by omega_arith),
        wv_out o₅ hC.dVX₂.symm (by omega_arith) (by omega_arith) hZ' hC.hV, wv_out o₄ hC.dVX₂.symm (by omega_arith) (by omega_arith) hZ' hC.hV,
        wv_out o₃ hC.dVX₂.symm (by omega_arith) (by omega_arith) hZ' hC.hV]
      have := V₂n.trans fabs
      exact_mod_cast this
    refine ⟨Vt, ?_⟩
    -- `±a` in `x₂`.
    have A₂ : wv s₂.mem C.B (slot C.w C.iX₂) (C.n + 1) = wv s.mem C.B (slot C.w C.iX₂) (C.n + 1) := by
      rw [wv_out o₂ hC.dVX₂ (by omega_arith) (by omega_arith) hZ' hC.hX₂, m₁]
    rw [A₂] at e₃
    have A₃ := Divstep.sgn_cneg hL (wv_lt _ _ _ _) (wv_lt _ _ _ _) (by rw [hav]; omega_arith) e₃
    rw [hav] at A₃
    set b0 := if f < 0 then -av else av with hb0
    have A₃' : sgn (C.n + 1) (wv s₃.mem C.B (slot C.w C.iX₂) (C.n + 1)) = b0 := by
      rw [A₃]
      by_cases h : f < 0
      · rw [ite_eq_left (decide_eq_true (hneg.mpr h)), hb0, ite_eq_left h]
      · rw [ite_eq_right (by simp only [decide_eq_true_eq]; exact fun h' => h (hneg.mp h')), hb0, ite_eq_right h]
    have b0r : -2 * (C.p : Int) < b0 ∧ b0 < 2 * C.p := by
      rw [hb0]; split <;> omega_arith
    -- `p` added if negative, twice.
    rw [M₃] at e₄
    have A₄ := addIfNeg_step (wsucc _ _) (wv_lt _ _ _ _) (BitVec.isLt _) e₄ (by rw [A₃']; split <;> omega_arith)
      (by rw [A₃']; split <;> omega_arith)
    rw [A₃'] at A₄
    set b1 := b0 + if b0 < 0 then (C.p : Int) else 0 with hb1
    have b1r : -(C.p : Int) < b1 ∧ b1 < 2 * C.p := by rw [hb1]; split <;> omega_arith
    rw [M₄] at e₅
    have A₅ := addIfNeg_step (wsucc _ _) (wv_lt _ _ _ _) (BitVec.isLt _) e₅ (by rw [A₄]; split <;> omega_arith)
      (by rw [A₄]; split <;> omega_arith)
    rw [A₄] at A₅
    set b2 := b1 + if b1 < 0 then (C.p : Int) else 0 with hb2
    have b2r : 0 ≤ b2 ∧ b2 < 2 * C.p := by rw [hb2]; split <;> omega_arith
    -- `a mod p`.
    have A₅v : (wv s₅.mem C.B (slot C.w C.iX₂) (C.n + 1) : Int) = b2 := by
      unfold sgn at A₅
      split at A₅
      · exact A₅
      · have := wv_lt s₅.mem C.B (slot C.w C.iX₂) (C.n + 1)
        have : ((wv s₅.mem C.B (slot C.w C.iX₂) (C.n + 1) : Nat) : Int) < 2 ^ (64 * (C.n + 1)) := by
          exact_mod_cast this
        omega_arith
    have hlt5 : wv s₅.mem C.B (slot C.w C.iX₂) (C.n + 1) < 2 * wv s₅.mem C.B (slot C.w C.iM) C.n := by
      rw [M₅]; have := b2r.2; rw [← A₅v] at this; exact_mod_cast this
    have e₆' := e₆ hlt5
    rw [M₅] at e₆'
    set r := wv s₅.mem C.B (slot C.w C.iX₂) (C.n + 1) % C.p with hr
    have rp : r < C.p := Nat.mod_lt _ (by omega_arith)
    have r6 : wv s₆.mem C.B (slot C.w C.iX₂) C.n = r := by
      have h6 := wsucc s₆.mem C.iX₂
      rw [e₆'] at h6
      have := wv_lt s₆.mem C.B (slot C.w C.iX₂) C.n
      have : 2 ^ (64 * C.n) * (word s₆.mem C.B (slot C.w C.iX₂ + 8 * C.n)).toNat = 0 := by
        rcases Nat.eq_zero_or_pos (word s₆.mem C.B (slot C.w C.iX₂ + 8 * C.n)).toNat with h | h
        · rw [h, Nat.mul_zero]
        · have := Nat.mul_le_mul_left (2 ^ (64 * C.n)) h; omega_arith
      omega_arith
    -- The doublings.
    have r7 : wv s₇.mem C.B (slot C.w C.iX₂) C.n = r := by rw [m₇, r6]
    have x₂t : wv t.mem C.B (slot C.w C.iX₂) C.n = r * 2 ^ (15 * C.n + 10) % C.p := by
      rw [mt, hD.val (by rw [r7, M₇]; exact rp), r7, M₇]
    rw [x₂t, show 15 * C.n + 10 = 5 * (3 * C.n + 2) by omega_arith]
    refine ⟨rr r ?_, Nat.mod_lt _ (by omega_arith)⟩
    -- `r ≡ ±a (mod p)`.
    have : (r : Int) = b2 % C.p := by rw [hr, Int.natCast_emod, A₅v]
    rw [this]
    refine (Int.mod_modEq _ _).trans ?_
    have e : b2 ≡ b0 [ZMOD (C.p : Int)] := by
      rw [hb2, hb1]
      split <;> split <;> simp [Int.ModEq, Int.add_emod_right]
    exact e


/-- `m ∣ (y mod m) a - g` gives `m ∣ y a - g`, for `y = r 2^K`. -/
theorem dvd_mod_mul {p r K a g : Nat} (h : (p : Int) ∣ ((r * 2 ^ K % p : Nat) : Int) * a - g) :
    (p : Int) ∣ (r : Int) * 2 ^ K * a - g := by
  have e' : ((r * 2 ^ K % p : Nat) : Int) + p * ((r * 2 ^ K / p : Nat) : Int) = (r : Int) * 2 ^ K := by
    exact_mod_cast Nat.mod_add_div (r * 2 ^ K) p
  rw [show (r : Int) * 2 ^ K * a - g = (((r * 2 ^ K % p : Nat) : Int) * a - g) +
      p * (((r * 2 ^ K / p : Nat) : Int) * a) by rw [← e']; ring]
  exact h.add (Dvd.intro _ rfl)

/-- `batchFinishS`: `batchFinish` without the doublings, `x₂ 2^(5 B)` the
inverse. -/
theorem finishS_ok {C : ICfg} (hC : C.Ok) {s₀ s : State} (hI : LInv C s₀ (3 * C.n + 2) s) :
    WP isa (seqs (batchFinishS C.iV C.iX₂ C.iM C.iT)) s fun t =>
      Scr t C.B C.Z ∧ t.gpr .x0 = C.B ∧ t.gpr .x1 = s₀.gpr .x1 ∧ t.gpr .x2 = s₀.gpr .x2 ∧
      t.gpr .x11 = BitVec.ofNat 64 (8 * (C.w + 2)) ∧ t.gpr .x12 = BitVec.ofNat 64 C.n ∧
      Frm C.B C.ranges s₀.mem t.mem ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s₀ t ∧
      (C.Good → ∀ a, a < 2 ^ (64 * C.n) → C.x = Rsa.Divstep.oddInput C.p a →
        wv t.mem C.B (slot C.w C.iV) C.n = Nat.gcd C.p a ∧
        (C.p : Int) ∣ (wv t.mem C.B (slot C.w C.iX₂) C.n : Int) * 2 ^ (5 * (3 * C.n + 2)) * a - Nat.gcd C.p a ∧
        wv t.mem C.B (slot C.w C.iX₂) C.n < C.p) := by
  have hn' := hI.scr.nowrap
  have hn1 := hC.n1; have hnw := hC.nw; have hw := hC.w24; have hZ := hC.hZ
  have hZ' : slot C.w 16 + C.B.toNat ≤ 2 ^ 64 := by omega_arith
  have sl : ∀ j < 16, slot C.w j + 8 * (C.w + 2) ≤ C.Z := fun j hj => Nat.le_trans (slot_lt (w := C.w) hj) hZ
  have sV := sl _ hC.hV; have sX₂ := sl _ hC.hX₂; have sM := sl _ hC.hM
  have rg : ∀ {j : Nat} {len : Nat}, (slot C.w j, 8 * (C.w + 2)) ∈ C.ranges → len ≤ 8 * (C.w + 2) →
      ∀ {m m' : Mem}, Outside C.B (slot C.w j) len m m' → Frm C.B C.ranges m m' := fun {j len} hr hl {m m'} o =>
    Frm.of_outside (Outside.mono (o' := slot C.w j) (n' := 8 * (C.w + 2)) o (Nat.le_refl _) (by omega_arith)) hr
  have rV : (slot C.w C.iV, 8 * (C.w + 2)) ∈ C.ranges := by simp [ICfg.ranges]
  have rX₂ : (slot C.w C.iX₂, 8 * (C.w + 2)) ∈ C.ranges := by simp [ICfg.ranges]
  have rT : (slot C.w C.iT, 8 * (C.w + 2)) ∈ C.ranges := by simp [ICfg.ranges]
  unfold batchFinishS
  rw [show ([Code.block (signMask C.iV), cnegP C.iV, cnegP C.iX₂] ++ addIfNeg C.iX₂ C.iM ++ addIfNeg C.iX₂ C.iM ++
      csubP C.iX₂ C.iM C.iT ++ [.block [.umov .x .x1 .v19 0, .umov .x .x2 .v19 1,
      .vop (.movi0 .v16), .vop (.movi0 .v17), .vop (.movi0 .v18), .vop (.movi0 .v19), .vop (.movi0 .v20), .vop (.movi0 .v21), .vop (.movi0 .v22), .vop (.movi0 .v23), .vop (.movi0 .v24), .vop (.movi0 .v25), .vop (.movi0 .v26)]] :
      List (Prog isa)) = [Code.block (signMask C.iV), cnegP C.iV, cnegP C.iX₂] ++ (addIfNeg C.iX₂ C.iM ++
      (addIfNeg C.iX₂ C.iM ++ (csubP C.iX₂ C.iM C.iT ++ [.block [.umov .x .x1 .v19 0, .umov .x .x2 .v19 1,
      .vop (.movi0 .v16), .vop (.movi0 .v17), .vop (.movi0 .v18), .vop (.movi0 .v19), .vop (.movi0 .v20), .vop (.movi0 .v21), .vop (.movi0 .v22), .vop (.movi0 .v23), .vop (.movi0 .v24), .vop (.movi0 .v25), .vop (.movi0 .v26)]])))
      by simp only [List.append_assoc]]
  refine wp_seqs_append (by simp) (by simp [addIfNeg]) ?_
  simp only [seqs]
  -- The sign of `f` into `x15`.
  refine WP.seq (WP.mono (signMask_ok hI.scr C.iV hI.x0 hI.x11 hI.x12 hnw hw hC.hV hZ)
    fun s₁ ⟨⟨h15, h7, m₁, v₁⟩, k₁⟩ => ?_)
  rw [signMask_mask] at h15
  have k01 := k₁
  -- `f := |f|`, `a := ±a`.
  refine WP.seq (WP.mono (cnegP_ok (hI.scr.congr k₁.wr) ((k₁.gpr .x0 (by decide)).trans hI.x0)
    ((k₁.gpr .x11 (by decide)).trans hI.x11) ((k₁.gpr .x12 (by decide)).trans hI.x12) hnw hw hZ hC.hV h15)
    fun s₂ ⟨e₂, o₂, k₂, v₂⟩ => ?_)
  have k02 := k01.trans k₂
  refine WP.mono (cnegP_ok (hI.scr.congr (k₁.trans k₂).wr) ((k02.gpr .x0 (by decide)).trans hI.x0)
    ((k02.gpr .x11 (by decide)).trans hI.x11) ((k02.gpr .x12 (by decide)).trans hI.x12) hnw hw hZ hC.hX₂
    ((k₂.gpr .x15 (by decide)).trans h15)) fun s₃ ⟨e₃, o₃, k₃, v₃⟩ => ?_
  have k03 := k02.trans k₃
  have sc₃ : Scr s₃ C.B C.Z := hI.scr.congr ((k₁.trans k₂).trans k₃).wr
  -- `p` added to `a` twice if negative.
  refine wp_seqs_append (by simp [addIfNeg]) (by simp [addIfNeg]) (WP.mono (addIfNeg_ok sc₃
    ((k03.gpr .x0 (by decide)).trans hI.x0) ((k03.gpr .x11 (by decide)).trans hI.x11)
    ((k03.gpr .x12 (by decide)).trans hI.x12) hn1 hnw hw hZ hC.hX₂ hC.hM hC.dX₂M) fun s₄ ⟨e₄, o₄, k₄, v₄⟩ => ?_)
  have k04 := k03.trans k₄
  have sc₄ : Scr s₄ C.B C.Z := sc₃.congr k₄.wr
  refine wp_seqs_append (by simp [addIfNeg]) (by simp [csubP]) (WP.mono (addIfNeg_ok sc₄
    ((k04.gpr .x0 (by decide)).trans hI.x0) ((k04.gpr .x11 (by decide)).trans hI.x11)
    ((k04.gpr .x12 (by decide)).trans hI.x12) hn1 hnw hw hZ hC.hX₂ hC.hM hC.dX₂M) fun s₅ ⟨e₅, o₅, k₅, v₅⟩ => ?_)
  have k05 := k04.trans k₅
  have sc₅ : Scr s₅ C.B C.Z := sc₄.congr k₅.wr
  -- `a mod p`.
  refine wp_seqs_append (by simp [csubP]) (by simp) (WP.mono (csubP_ok sc₅
    ((k05.gpr .x0 (by decide)).trans hI.x0) ((k05.gpr .x11 (by decide)).trans hI.x11)
    ((k05.gpr .x12 (by decide)).trans hI.x12) hn1 hnw hw hZ hC.hX₂ hC.hM hC.hT hC.dX₂M hC.dX₂T hC.dMT)
    fun s₆ ⟨e₆, f₆, k₆, v₆⟩ => ?_)
  have k06 := k05.trans k₆
  have sc₆ : Scr s₆ C.B C.Z := sc₅.congr k₆.wr
  simp only [seqs]
  -- `x1`, `x2` back.
  refine WP.mono (WP.keep [.x1, .x2] (Q := fun t => t.gpr .x1 = (s₆.v .v19).extractLsb' 0 64 ∧
      t.gpr .x2 = (s₆.v .v19).extractLsb' 64 64 ∧ t.mem = s₆.mem)
    (by brun [exec_umov_x, exec_movi0, RegUpd.v_write, RegUpd.gpr_setV, RegUpd.mem_setV, Nat.mul_zero,
      Nat.mul_one]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨t1, t2, mt⟩, kt⟩ => ?_
  have k0t := hI.keep.trans (k06.trans kt)
  have vv : s₆.v = s.v := by rw [v₆, v₅, v₄, v₃, v₂, v₁]
  refine ⟨sc₆.congr kt.wr, (kt.gpr .x0 (by decide)).trans ((k06.gpr .x0 (by decide)).trans hI.x0), ?_, ?_,
    (kt.gpr .x11 (by decide)).trans ((k06.gpr .x11 (by decide)).trans hI.x11),
    (kt.gpr .x12 (by decide)).trans ((k06.gpr .x12 (by decide)).trans hI.x12), ?_, k0t.mono (by decide), ?_⟩
  · rw [t1, vv]; exact hI.x1s
  · rw [t2, vv]; exact hI.x2s
  · have w6 : Frm C.B C.ranges s₅.mem s₆.mem := Frm.widen f₆ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, rX₂, Nat.le_refl _, by dsimp only; omega_arith⟩
      · exact ⟨_, rT, Nat.le_refl _, by dsimp only; omega_arith⟩
    rw [mt]
    refine hI.frm.trans ?_
    rw [m₁] at o₂
    exact ((((rg rV (by omega_arith) o₂).trans (rg rX₂ (by omega_arith) o₃)).trans (rg rX₂ (by omega_arith) o₄)).trans
      (rg rX₂ (by omega_arith) o₅)).trans w6
  · intro G a ha hx
    have hL : 1 ≤ C.n + 1 := by omega_arith
    have hpf : C.pf = C.p := by unfold ICfg.pf; have := G.1; omega_arith
    have hm' : ((C.p : Int) * C.mi.toNat + 1) % 2 ^ 64 = 0 := by
      have := hC.hm; rw [show C.p + (1 - C.p % 2) = C.p by have := G.1; omega_arith] at this; exact this
    have hp1 : (1 : Int) < C.p := by exact_mod_cast G.2
    have est : C.st (3 * C.n + 2) =
        Divstep.invRunS 59 C.p C.mi.toNat (Rsa.Divstep.oddInput C.p a) (3 * C.n + 2) := by
      unfold ICfg.st; rw [hpf, hx]
    obtain ⟨-, rf0, rr⟩ := Rsa.Divstep.invRunS59_result (mi := C.mi.toNat) G.1 hm' hC.pC ha
    obtain ⟨ra0, ra1, -, -⟩ := Divstep.invRunS_range (N := 59) (p := C.p) (m := C.mi.toNat)
      (x := Rsa.Divstep.oddInput C.p a) (by decide) hp1 hm' (3 * C.n + 2)
    rw [← est] at rf0 rr ra0 ra1
    have hf := hI.f
    have hav := hI.a G
    set f := (C.st (3 * C.n + 2)).f with hfdef
    set av := (C.st (3 * C.n + 2)).a with hadef
    have gp : Nat.gcd C.p a ≤ C.p := Nat.gcd_le_left _ (by omega_arith)
    have pC := hC.pC
    have half : (2 : Int) ^ (64 * C.n) * 2 ≤ 2 ^ (64 * (C.n + 1) - 1) := by
      have : 2 ^ (64 * C.n) * 2 ≤ 2 ^ (64 * (C.n + 1) - 1) := by
        rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) (by omega_arith)
      exact_mod_cast this
    have pC' : (C.p : Int) < 2 ^ (64 * C.n) := by exact_mod_cast pC
    have fabs : |f| = (Nat.gcd C.p a : Int) := by rw [← Int.natCast_natAbs, rf0]
    have fabs' : |f| < 2 ^ (64 * C.n) := by rw [fabs]; omega_arith
    -- Memory between the stages.
    have M₀ := hI.m
    have wsucc : ∀ (m : Mem) (j : Nat), wv m C.B (slot C.w j) (C.n + 1) =
        wv m C.B (slot C.w j) C.n + 2 ^ (64 * C.n) * (word m C.B (slot C.w j + 8 * C.n)).toNat := fun m j => by
      rw [wv]
    have M₃ : wv s₃.mem C.B (slot C.w C.iM) C.n = C.p := by
      rw [wv_out o₃ hC.dX₂M (by omega_arith) (by omega_arith) hZ' hC.hM, wv_out o₂ hC.dVM (by omega_arith) (by omega_arith) hZ' hC.hM, m₁, M₀]
    have M₄ : wv s₄.mem C.B (slot C.w C.iM) C.n = C.p := by
      rw [wv_out o₄ hC.dX₂M (by omega_arith) (by omega_arith) hZ' hC.hM, M₃]
    have M₅ : wv s₅.mem C.B (slot C.w C.iM) C.n = C.p := by
      rw [wv_out o₅ hC.dX₂M (by omega_arith) (by omega_arith) hZ' hC.hM, M₄]
    -- `|f|` in `v`.
    have hneg : (2 ^ 63 ≤ (word s.mem C.B (slot C.w C.iV + 8 * C.n)).toNat) ↔ f < 0 := by
      rw [← hf, wsucc]
      exact (Divstep.sgn_neg_iff (wv_lt _ _ _ _) (BitVec.isLt _)).symm
    rw [m₁] at e₂
    have V₂ := Divstep.sgn_cneg hL (wv_lt _ _ _ _) (wv_lt _ _ _ _) (by rw [hf]; omega_arith) e₂
    rw [hf] at V₂
    have V₂' : sgn (C.n + 1) (wv s₂.mem C.B (slot C.w C.iV) (C.n + 1)) = |f| := by
      rw [V₂]
      by_cases h : f < 0
      · rw [ite_eq_left (decide_eq_true (hneg.mpr h)), abs_of_neg h]
      · rw [ite_eq_right (by simp only [decide_eq_true_eq]; exact fun h' => h (hneg.mp h')), abs_of_nonneg (by omega_arith)]
    obtain ⟨-, V₂n⟩ := small_of_sgn (wsucc _ _) (wv_lt _ _ _ _) (BitVec.isLt _) V₂' (abs_nonneg _) fabs'
    have apV6 : ∀ r ∈ [(slot C.w C.iX₂, 8 * (C.n + 1)), (slot C.w C.iT, 8 * C.n)],
        slot C.w C.iV + 8 * C.n ≤ r.1 ∨ r.1 + r.2 ≤ slot C.w C.iV := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slot_apart (w := C.w) hC.dVX₂ (by omega_arith) (by omega_arith)
      · exact slot_apart (w := C.w) hC.dVT (by omega_arith) (by omega_arith)
    have Vt : wv t.mem C.B (slot C.w C.iV) C.n = Nat.gcd C.p a := by
      rw [mt, f₆.wv_eq apV6 (by omega_arith),
        wv_out o₅ hC.dVX₂.symm (by omega_arith) (by omega_arith) hZ' hC.hV, wv_out o₄ hC.dVX₂.symm (by omega_arith) (by omega_arith) hZ' hC.hV,
        wv_out o₃ hC.dVX₂.symm (by omega_arith) (by omega_arith) hZ' hC.hV]
      have := V₂n.trans fabs
      exact_mod_cast this
    refine ⟨Vt, ?_⟩
    -- `±a` in `x₂`.
    have A₂ : wv s₂.mem C.B (slot C.w C.iX₂) (C.n + 1) = wv s.mem C.B (slot C.w C.iX₂) (C.n + 1) := by
      rw [wv_out o₂ hC.dVX₂ (by omega_arith) (by omega_arith) hZ' hC.hX₂, m₁]
    rw [A₂] at e₃
    have A₃ := Divstep.sgn_cneg hL (wv_lt _ _ _ _) (wv_lt _ _ _ _) (by rw [hav]; omega_arith) e₃
    rw [hav] at A₃
    set b0 := if f < 0 then -av else av with hb0
    have A₃' : sgn (C.n + 1) (wv s₃.mem C.B (slot C.w C.iX₂) (C.n + 1)) = b0 := by
      rw [A₃]
      by_cases h : f < 0
      · rw [ite_eq_left (decide_eq_true (hneg.mpr h)), hb0, ite_eq_left h]
      · rw [ite_eq_right (by simp only [decide_eq_true_eq]; exact fun h' => h (hneg.mp h')), hb0, ite_eq_right h]
    have b0r : -2 * (C.p : Int) < b0 ∧ b0 < 2 * C.p := by
      rw [hb0]; split <;> omega_arith
    -- `p` added if negative, twice.
    rw [M₃] at e₄
    have A₄ := addIfNeg_step (wsucc _ _) (wv_lt _ _ _ _) (BitVec.isLt _) e₄ (by rw [A₃']; split <;> omega_arith)
      (by rw [A₃']; split <;> omega_arith)
    rw [A₃'] at A₄
    set b1 := b0 + if b0 < 0 then (C.p : Int) else 0 with hb1
    have b1r : -(C.p : Int) < b1 ∧ b1 < 2 * C.p := by rw [hb1]; split <;> omega_arith
    rw [M₄] at e₅
    have A₅ := addIfNeg_step (wsucc _ _) (wv_lt _ _ _ _) (BitVec.isLt _) e₅ (by rw [A₄]; split <;> omega_arith)
      (by rw [A₄]; split <;> omega_arith)
    rw [A₄] at A₅
    set b2 := b1 + if b1 < 0 then (C.p : Int) else 0 with hb2
    have b2r : 0 ≤ b2 ∧ b2 < 2 * C.p := by rw [hb2]; split <;> omega_arith
    -- `a mod p`.
    have A₅v : (wv s₅.mem C.B (slot C.w C.iX₂) (C.n + 1) : Int) = b2 := by
      unfold sgn at A₅
      split at A₅
      · exact A₅
      · have := wv_lt s₅.mem C.B (slot C.w C.iX₂) (C.n + 1)
        have : ((wv s₅.mem C.B (slot C.w C.iX₂) (C.n + 1) : Nat) : Int) < 2 ^ (64 * (C.n + 1)) := by
          exact_mod_cast this
        omega_arith
    have hlt5 : wv s₅.mem C.B (slot C.w C.iX₂) (C.n + 1) < 2 * wv s₅.mem C.B (slot C.w C.iM) C.n := by
      rw [M₅]; have := b2r.2; rw [← A₅v] at this; exact_mod_cast this
    have e₆' := e₆ hlt5
    rw [M₅] at e₆'
    set r := wv s₅.mem C.B (slot C.w C.iX₂) (C.n + 1) % C.p with hr
    have rp : r < C.p := Nat.mod_lt _ (by omega_arith)
    have r6 : wv s₆.mem C.B (slot C.w C.iX₂) C.n = r := by
      have h6 := wsucc s₆.mem C.iX₂
      rw [e₆'] at h6
      have := wv_lt s₆.mem C.B (slot C.w C.iX₂) C.n
      have : 2 ^ (64 * C.n) * (word s₆.mem C.B (slot C.w C.iX₂ + 8 * C.n)).toNat = 0 := by
        rcases Nat.eq_zero_or_pos (word s₆.mem C.B (slot C.w C.iX₂ + 8 * C.n)).toNat with h | h
        · rw [h, Nat.mul_zero]
        · have := Nat.mul_le_mul_left (2 ^ (64 * C.n)) h; omega_arith
      omega_arith
    have x₂t : wv t.mem C.B (slot C.w C.iX₂) C.n = r := by rw [mt, r6]
    rw [x₂t]
    refine ⟨dvd_mod_mul (rr r ?_), rp⟩
    -- `r ≡ ±a (mod p)`.
    have : (r : Int) = b2 % C.p := by rw [hr, Int.natCast_emod, A₅v]
    rw [this]
    refine (Int.mod_modEq _ _).trans ?_
    have e : b2 ≡ b0 [ZMOD (C.p : Int)] := by
      rw [hb2, hb1]
      split <;> split <;> simp [Int.ModEq, Int.add_emod_right]
    exact e


/-- `-q⁻¹ mod 2^64` exists for an odd `q`. -/
theorem minv_exists {q : Nat} (hq : q % 2 = 1) : ∃ mi : BitVec 64, ((q : Int) * mi.toNat + 1) % 2 ^ 64 = 0 := by
  have hc : Nat.Coprime q (2 ^ 64) := Nat.Coprime.pow_right _ (by
    show Nat.gcd q 2 = 1
    rw [Nat.gcd_comm, Nat.gcd_rec, hq]; rfl)
  obtain ⟨m, hm, hqm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hc (by decide)
  have m0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hqm
    · exact h
  refine ⟨BitVec.ofNat 64 (2 ^ 64 - m), ?_⟩
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have hk := Nat.div_add_mod (q * m) (2 ^ 64)
  rw [hqm] at hk
  set k := q * m / 2 ^ 64
  have e : ((q : Int) * ((2 ^ 64 - m : Nat) : Int) + 1) = 2 ^ 64 * ((q : Int) - k) := by
    have hk' : ((q : Int) * m) = 2 ^ 64 * k + 1 := by exact_mod_cast hk.symm
    rw [Nat.cast_sub (show m ≤ 2 ^ 64 by omega_arith)]
    push_cast
    linarith
  rw [e]; exact Int.mul_emod_right _ _

/-- The batched inverse at the width `n` in `x12` (`x11` the stride of
arrays of `w` words), for `[v] = [m] = p` and `[u] = a`: `x1`, `x2` kept,
only the arrays `u`, `v`, `x₁`, `x₂` and `t` changed, and for an odd
`p > 1`, `[v] = gcd(p, a)`, `p ∣ [x₂] a - gcd(p, a)` and `[x₂] < p`. -/
theorem inverseB_ok {s : State} {B : Addr} {Z w n : Nat} {iU iV iX₁ iX₂ iM iT : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hn1 : 1 ≤ n) (hnw : n ≤ w) (hw : w < 2 ^ 24) (hn21 : n < 2 ^ 21) (hZ : slot w 16 ≤ Z)
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dUV : iU ≠ iV) (dUX₁ : iU ≠ iX₁) (dUX₂ : iU ≠ iX₂) (dUM : iU ≠ iM) (dUT : iU ≠ iT) (dVX₁ : iV ≠ iX₁)
    (dVX₂ : iV ≠ iX₂) (dVM : iV ≠ iM) (dVT : iV ≠ iT) (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT)
    (dX₂M : iX₂ ≠ iM) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT)
    (hVM : wv s.mem B (slot w iV) n = wv s.mem B (slot w iM) n) :
    WP isa (inverseB iU iV iX₁ iX₂ iM iT) s fun t =>
      Scr t B Z ∧ t.gpr .x0 = B ∧ t.gpr .x1 = s.gpr .x1 ∧ t.gpr .x2 = s.gpr .x2 ∧
      t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .x12 = BitVec.ofNat 64 n ∧
      Frm B [(slot w iU, 8 * (w + 2)), (slot w iV, 8 * (w + 2)), (slot w iX₁, 8 * (w + 2)),
        (slot w iX₂, 8 * (w + 2)), (slot w iT, 8 * (w + 2))] s.mem t.mem ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s t ∧
      (wv s.mem B (slot w iM) n % 2 = 1 → 1 < wv s.mem B (slot w iM) n →
        wv t.mem B (slot w iV) n = Nat.gcd (wv s.mem B (slot w iM) n) (wv s.mem B (slot w iU) n) ∧
        (wv s.mem B (slot w iM) n : Int) ∣ (wv t.mem B (slot w iX₂) n : Int) * wv s.mem B (slot w iU) n -
          Nat.gcd (wv s.mem B (slot w iM) n) (wv s.mem B (slot w iU) n) ∧
        wv t.mem B (slot w iX₂) n < wv s.mem B (slot w iM) n) := by
  set p := wv s.mem B (slot w iM) n with hp
  set a := wv s.mem B (slot w iU) n with ha
  have pC : p < 2 ^ (64 * n) := wv_lt _ _ _ _
  have aC : a < 2 ^ (64 * n) := wv_lt _ _ _ _
  obtain ⟨mi, hmi⟩ := minv_exists (q := p + (1 - p % 2)) (by omega_arith)
  let C : ICfg := ⟨B, Z, w, n, iU, iV, iX₁, iX₂, iM, iT, p, mi, Rsa.Divstep.oddInput p a⟩
  have hC : C.Ok := ⟨hn1, hnw, hw, hn21, hZ, hU, hV, hX₁, hX₂, hM, hT, dUV, dUX₁, dUX₂, dUM, dUT, dVX₁, dVX₂, dVM,
    dVT, dX, dX₁M, dX₁T, dX₂M, dX₂T, dMT, pC,
    by
      have := Rsa.Divstep.oddInput_lt (m := p) (x := a) pC aC
      show Rsa.Divstep.oddInput p a < 2 ^ (64 * n + 1)
      rw [Nat.pow_succ]; omega_arith,
    by exact_mod_cast hmi⟩
  unfold inverseB
  rw [List.append_assoc]
  refine wp_seqs_append (by simp [batchInit]) (by simp) (WP.mono (batchInit_ok (C := C) hC hs h0 h11 h12 hVM rfl rfl rfl)
    fun s₁ ⟨hI₁, h15⟩ => ?_)
  rw [List.singleton_append]
  have hf : batchFinish iV iU iX₂ iM iT ≠ [] := by simp [batchFinish]
  obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hf
  rw [hcs]
  simp only [seqs]
  rw [← hcs]
  refine WP.seq (WP.mono (batches_ok hC hI₁ h15) fun s₂ hI₂ => WP.mono (finish_ok hC hI₂) fun t ⟨sc, t0, t1, t2, t11,
    t12, fr, kt, val⟩ => ⟨sc, t0, t1, t2, t11, t12, fr, kt, fun h1 h2 => ?_⟩)
  obtain ⟨v1, v2, v3⟩ := val ⟨h1, h2⟩ a aC rfl
  exact ⟨v1, v2, v3⟩


/-- `inverseBS`: `inverseB_ok` with `x₂ 2^(5 B)` the inverse. -/
theorem inverseBS_ok {s : State} {B : Addr} {Z w n : Nat} {iU iV iX₁ iX₂ iM iT : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hn1 : 1 ≤ n) (hnw : n ≤ w) (hw : w < 2 ^ 24) (hn21 : n < 2 ^ 21) (hZ : slot w 16 ≤ Z)
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dUV : iU ≠ iV) (dUX₁ : iU ≠ iX₁) (dUX₂ : iU ≠ iX₂) (dUM : iU ≠ iM) (dUT : iU ≠ iT) (dVX₁ : iV ≠ iX₁)
    (dVX₂ : iV ≠ iX₂) (dVM : iV ≠ iM) (dVT : iV ≠ iT) (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT)
    (dX₂M : iX₂ ≠ iM) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT)
    (hVM : wv s.mem B (slot w iV) n = wv s.mem B (slot w iM) n) :
    WP isa (inverseBS iU iV iX₁ iX₂ iM iT) s fun t =>
      Scr t B Z ∧ t.gpr .x0 = B ∧ t.gpr .x1 = s.gpr .x1 ∧ t.gpr .x2 = s.gpr .x2 ∧
      t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .x12 = BitVec.ofNat 64 n ∧
      Frm B [(slot w iU, 8 * (w + 2)), (slot w iV, 8 * (w + 2)), (slot w iX₁, 8 * (w + 2)),
        (slot w iX₂, 8 * (w + 2)), (slot w iT, 8 * (w + 2))] s.mem t.mem ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s t ∧
      (wv s.mem B (slot w iM) n % 2 = 1 → 1 < wv s.mem B (slot w iM) n →
        wv t.mem B (slot w iV) n = Nat.gcd (wv s.mem B (slot w iM) n) (wv s.mem B (slot w iU) n) ∧
        (wv s.mem B (slot w iM) n : Int) ∣ (wv t.mem B (slot w iX₂) n : Int) * 2 ^ (5 * (3 * n + 2)) *
          wv s.mem B (slot w iU) n -
          Nat.gcd (wv s.mem B (slot w iM) n) (wv s.mem B (slot w iU) n) ∧
        wv t.mem B (slot w iX₂) n < wv s.mem B (slot w iM) n) := by
  set p := wv s.mem B (slot w iM) n with hp
  set a := wv s.mem B (slot w iU) n with ha
  have pC : p < 2 ^ (64 * n) := wv_lt _ _ _ _
  have aC : a < 2 ^ (64 * n) := wv_lt _ _ _ _
  obtain ⟨mi, hmi⟩ := minv_exists (q := p + (1 - p % 2)) (by omega_arith)
  let C : ICfg := ⟨B, Z, w, n, iU, iV, iX₁, iX₂, iM, iT, p, mi, Rsa.Divstep.oddInput p a⟩
  have hC : C.Ok := ⟨hn1, hnw, hw, hn21, hZ, hU, hV, hX₁, hX₂, hM, hT, dUV, dUX₁, dUX₂, dUM, dUT, dVX₁, dVX₂, dVM,
    dVT, dX, dX₁M, dX₁T, dX₂M, dX₂T, dMT, pC,
    by
      have := Rsa.Divstep.oddInput_lt (m := p) (x := a) pC aC
      show Rsa.Divstep.oddInput p a < 2 ^ (64 * n + 1)
      rw [Nat.pow_succ]; omega_arith,
    by exact_mod_cast hmi⟩
  unfold inverseBS
  rw [List.append_assoc]
  refine wp_seqs_append (by simp [batchInit]) (by simp) (WP.mono (batchInit_ok (C := C) hC hs h0 h11 h12 hVM rfl rfl rfl)
    fun s₁ ⟨hI₁, h15⟩ => ?_)
  rw [List.singleton_append]
  have hf : batchFinishS iV iX₂ iM iT ≠ [] := by simp [batchFinishS]
  obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hf
  rw [hcs]
  simp only [seqs]
  rw [← hcs]
  refine WP.seq (WP.mono (batches_ok hC hI₁ h15) fun s₂ hI₂ => WP.mono (finishS_ok hC hI₂) fun t ⟨sc, t0, t1, t2, t11,
    t12, fr, kt, val⟩ => ⟨sc, t0, t1, t2, t11, t12, fr, kt, fun h1 h2 => ?_⟩)
  obtain ⟨v1, v2, v3⟩ := val ⟨h1, h2⟩ a aC rfl
  exact ⟨v1, v2, v3⟩


/-- `x1`, `x2` back: the registers `Keep` names for `inverse`. -/
theorem keep_restore {s t : State} (k : Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13,
    .x14, .x15, .x16, .x17] s t) (h1 : t.gpr .x1 = s.gpr .x1) (h2 : t.gpr .x2 = s.gpr .x2) :
    Keep (.x11 :: .x12 :: stepRegs) s t :=
  ⟨fun r hr => by
    by_cases e1 : r = .x1
    · subst e1; exact h1
    by_cases e2 : r = .x2
    · subst e2; exact h2
    exact k.gpr r (by revert hr e1 e2; cases r <;> decide), k.rd, k.wr, k.sp, k.vcs⟩

/-- `inverse u v x₁ x₂ m t`, at the header's width `w`: by batches of
divsteps (`inverseB_ok`) for `w < 2^21`, else bit by bit (`inverseBits_ok`):
`[v] = gcd(a, m)`, `m ∣ [x₂] a - [v]` and `[x₂] < m` for `[u] = a` and the
odd `[m] = [v] > 1`; only the arrays `u`, `v`, `x₁`, `x₂` and `t` change. -/
theorem inverse_ok {s : State} {B : Addr} {Z w : Nat} {iU iV iX₁ iX₂ iM iT : Nat} (h : Ws s B Z w)
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dUV : iU ≠ iV) (dUX₁ : iU ≠ iX₁) (dUX₂ : iU ≠ iX₂) (dUM : iU ≠ iM) (dUT : iU ≠ iT) (dVX₁ : iV ≠ iX₁)
    (dVX₂ : iV ≠ iX₂) (dVM : iV ≠ iM) (dVT : iV ≠ iT) (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT)
    (dX₂M : iX₂ ≠ iM) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT) (hU0 : word s.mem B (slot w iU + 8 * w) = 0)
    (hVM : wv s.mem B (slot w iV) w = wv s.mem B (slot w iM) w) (hX1 : wv s.mem B (slot w iX₁) w = 1)
    (hX2 : wv s.mem B (slot w iX₂) w = 0) :
    WP isa (inverse iU iV iX₁ iX₂ iM iT) s fun t =>
      t.gpr .x0 = B ∧ Frm B [ar w iU, ar w iV, ar w iX₁, ar w iX₂, ar w iT] s.mem t.mem ∧
      Keep (.x11 :: .x12 :: stepRegs) s t ∧
      (wv s.mem B (slot w iM) w % 2 = 1 → 1 < wv s.mem B (slot w iM) w →
        wv t.mem B (slot w iV) w = Nat.gcd (wv s.mem B (slot w iU) w) (wv s.mem B (slot w iM) w) ∧
        ((wv s.mem B (slot w iM) w : Nat) : Int) ∣
          (wv t.mem B (slot w iX₂) w : Int) * wv s.mem B (slot w iU) w - wv t.mem B (slot w iV) w ∧
        wv t.mem B (slot w iX₂) w < wv s.mem B (slot w iM) w) := by
  have hs := h.scr
  have hw1 := h.w1
  have hw := h.w2
  unfold inverse
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨⟨h12₁, h11₁, m₁, _⟩, k₁⟩ =>
    WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = s₁.gpr .x12 >>> 21 ∧ t.mem = s₁.mem)
      (by brun) (by decide) (by decide) (by decide +kernel)) fun s₂ ⟨⟨h3₂, m₂⟩, k₂⟩ => ?_))
  have k12 := k₁.trans k₂
  have hm₂ : s₂.mem = s.mem := by rw [m₂, m₁]
  have hs₂ : Scr s₂ B Z := hs.congr k12.wr
  have h0₂ : s₂.gpr .x0 = B := (k12.gpr .x0 (by decide)).trans h.x0
  have e3 : (s₂.gpr .x3).toNat = w / 2 ^ 21 := by
    rw [h3₂, h12₁, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_arith), Nat.shiftRight_eq_div_pow]
  refine WP.ite (decide (w < 2 ^ 21)) (by
      show some (s₂.read .x .x3 == 0) = _
      congr 1
      have : s₂.read .x .x3 = s₂.gpr .x3 := rfl
      rw [this]
      by_cases hw21 : w < 2 ^ 21
      · rw [decide_eq_true hw21, beq_iff_eq]
        apply BitVec.eq_of_toNat_eq; rw [e3]; simp; omega_arith
      · rw [decide_eq_false hw21]
        apply Bool.eq_false_iff.mpr
        intro hb
        rw [beq_iff_eq] at hb
        have := congrArg BitVec.toNat hb
        rw [e3] at this
        simp at this
        omega_arith) (fun hb => ?_) (fun hb => ?_)
  · -- Batches of divsteps.
    have hw21 : w < 2 ^ 21 := by simpa using hb
    refine WP.mono (inverseB_ok hs₂ h0₂ ((k₂.gpr .x11 (by decide)).trans h11₁) ((k₂.gpr .x12 (by decide)).trans h12₁)
      (by omega_arith) (Nat.le_refl _) hw hw21 h.hZ hU hV hX₁ hX₂ hM hT dUV dUX₁ dUX₂ dUM dUT dVX₁ dVX₂ dVM dVT dX dX₁M dX₁T
      dX₂M dX₂T dMT (by rw [hm₂]; exact hVM)) fun t ⟨_, t0, t1, t2, _, _, fr, kt, val⟩ => ?_
    rw [hm₂] at fr val
    refine ⟨t0, fr, ?_, fun h1 h2 => ?_⟩
    · have k := k12.trans kt
      exact keep_restore (k.mono (by decide)) (by rw [t1, k12.gpr .x1 (by decide)])
        (by rw [t2, k12.gpr .x2 (by decide)])
    · obtain ⟨v1, v2, v3⟩ := val h1 h2
      rw [Nat.gcd_comm] at v1 v2
      exact ⟨v1, by rw [v1]; exact v2, v3⟩
  · -- Bit by bit.
    have h₂ : Ws s₂ B Z w := h.congr (rs := []) (by rw [hm₂]; exact Frm.refl _ _ _) (by simp) k12 (by decide)
    refine WP.mono (inverseBits_ok h₂ hU hV hX₁ hX₂ hM hT dUV dUX₁ dUX₂ dUM dUT dVX₁ dVX₂ dVM dVT dX dX₁M dX₁T
      dX₂M dX₂T dMT (by rw [hm₂]; exact hU0) (by rw [hm₂]; exact hVM) (by rw [hm₂]; exact hX1)
      (by rw [hm₂]; exact hX2) ((k₂.gpr .x12 (by decide)).trans h12₁) ((k₂.gpr .x11 (by decide)).trans h11₁))
      fun t ⟨t0, fr, kt, val⟩ => ?_
    rw [hm₂] at fr val
    refine ⟨t0, Frm.widen fr fun r hr => ?_, (k12.trans kt).mono (by decide), val⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨ar w iU, by simp, Nat.le_refl _, Nat.add_le_add_left (show 8 * w ≤ 8 * (w + 2) by omega_arith) _⟩
    · exact ⟨ar w iV, by simp, Nat.le_refl _, Nat.add_le_add_left (show 8 * w ≤ 8 * (w + 2) by omega_arith) _⟩
    · exact ⟨ar w iX₁, by simp, Nat.le_refl _, Nat.add_le_add_left (show 8 * w ≤ 8 * (w + 2) by omega_arith) _⟩
    · exact ⟨ar w iX₂, by simp, Nat.le_refl _, Nat.add_le_add_left (show 8 * w ≤ 8 * (w + 2) by omega_arith) _⟩
    · exact ⟨ar w iT, by simp, Nat.le_refl _, Nat.le_refl _⟩

end VG.Proof.Rsa.AArch64

/-! ## At a narrower width, and the instance

`inverseAt nb`: `nCalc` (`⌈max(a, b) / 8⌉` from the header) or another
width block `nb`, the batches at that width (`inverseB_ok`), and the words
of `[v]` and `[x₂]` above it cleared (`tailZ_ok`): `inverseAt_ok`. Then
the instance of `InvLaw` the registrations use.
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.InvBatch
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)


/-- `tailZ j`: words `n` to `w + 1` of array `j` cleared, so that its `w`
words are its `n`. -/
theorem tailZ_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n) (hn : n ≤ w)
    (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {j : Nat} (hj : j < 16) :
    WP isa (seqs (tailZ j)) s fun t =>
      wv t.mem B (slot w j) w = wv s.mem B (slot w j) n ∧
      Outside B (slot w j) (8 * (w + 2)) s.mem t.mem ∧ t.v = s.v ∧
      Keep [.x3, .x7, .x8, .x13, .x14, .x16] s t := by
  have hn' := hs.nowrap
  have sj := Nat.le_trans (slot_lt (w := w) hj) hZ
  have hvn : (seqs (tailZ j)).allInstrs (fun i => (vdstOf i).isNone) = true := by
    simp only [tailZ, seqs, zeroAcc, countLoop, Code.allInstrs_eq, instrs, List.all_append, base_vnone]; decide
  refine WP.mono (WP.vfix (Q := fun t => wv t.mem B (slot w j) w = wv s.mem B (slot w j) n ∧
      Outside B (slot w j) (8 * (w + 2)) s.mem t.mem ∧ Keep [.x3, .x7, .x8, .x13, .x14, .x16] s t) ?_ hvn)
    fun t ⟨⟨a, b, c⟩, v⟩ => ⟨a, b, v, c⟩
  simp only [tailZ, seqs]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (base_ok j .x8 h0 h11) fun s₁ ⟨⟨h8, m₁, _⟩, k₁⟩ =>
    WP.mono (WP.keep [.x3, .x8, .x13, .x12, .x7] (Q := fun t => t.gpr .x8 = off B (slot w j + 8 * n) ∧
        t.gpr .x12 = BitVec.ofNat 64 (w - n) ∧ t.gpr .x3 = BitVec.ofNat 64 n ∧ t.gpr .x7 = 0 ∧ t.mem = s₁.mem)
      (by
        brun [h8, (k₁.gpr .x12 (by decide)).trans h12, (k₁.gpr .x11 (by decide)).trans h11,
          shl_ofNat (show n * 2 ^ 3 < 2 ^ 64 by omega_arith)]
        refine ⟨?_, ?_⟩
        · congr 2; omega_arith
        · apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
          omega_arith)
      (by decide) (by decide) (by decide +kernel)) fun s₂ ⟨⟨h8₂, h12₂, h3₂, h7₂, m₂⟩, k₂⟩ => ?_))
  have k12 := k₁.trans k₂
  refine WP.seq (WP.mono (zeroAcc_ok (hs.congr k12.wr) h8₂ h12₂ h7₂ (by omega_arith) (by omega_arith))
    fun s₃ ⟨z₃, o₃, k₃⟩ => ?_)
  refine WP.mono (WP.keep [.x12] (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 n ∧ t.mem = s₃.mem)
    (by brun [(k₃.gpr .x3 (by decide)).trans h3₂]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h12t, mt⟩, kt⟩ => ⟨?_, ?_, ?_⟩
  · have hm : s₂.mem = s.mem := by rw [m₂, m₁]
    have e := wv_add s₃.mem B (slot w j) n (w - n)
    rw [show n + (w - n) = w by omega_arith] at e
    rw [mt, e, o₃.wv (Or.inl (Nat.le_refl _)) (by omega_arith), hm]
    have z : wv s₃.mem B (slot w j + 8 * n) (w - n) = 0 := by
      have := wv_add s₃.mem B (slot w j + 8 * n) (w - n) 2
      rw [z₃] at this; omega_arith
    rw [z, Nat.mul_zero, Nat.add_zero]
  · rw [mt]
    intro x hx
    rw [o₃ x (by omega_arith), m₂, m₁]
  · refine ⟨fun r hr => ?_, kt.rd.trans (k₃.rd.trans k12.rd), kt.wr.trans (k₃.wr.trans k12.wr),
      kt.sp.trans (k₃.sp.trans k12.sp), fun r hr => (kt.vcs r hr).trans ((k₃.vcs r hr).trans (k12.vcs r hr))⟩
    by_cases e : r = .x12
    · subst e; rw [h12t, h12]
    · rw [kt.gpr r (by simpa using e), k₃.gpr r (by cases r <;> simp_all), k₂.gpr r (by cases r <;> simp_all),
        k₁.gpr r (by cases r <;> simp_all)]

/-- The first `n` words of `w`. -/
theorem wv_low_mod (m : Mem) (B : Addr) {d n w : Nat} (h : n ≤ w) :
    wv m B d n = wv m B d w % 2 ^ (64 * n) := by
  have e := wv_add m B d n (w - n)
  rw [show n + (w - n) = w by omega_arith] at e
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wv_lt _ _ _ _)]

/-- `inverseAt nb`: `inverse_ok`'s contract at the width `n` of `nb`. -/
theorem inverseAt_ok {s : State} {B : Addr} {Z w n : Nat} {nb : List Instr} {iU iV iX₁ iX₂ iM iT : Nat}
    (h : Ws s B Z w)
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dUV : iU ≠ iV) (dUX₁ : iU ≠ iX₁) (dUX₂ : iU ≠ iX₂) (dUM : iU ≠ iM) (dUT : iU ≠ iT) (dVX₁ : iV ≠ iX₁)
    (dVX₂ : iV ≠ iX₂) (dVM : iV ≠ iM) (dVT : iV ≠ iT) (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT)
    (dX₂M : iX₂ ≠ iM) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT) (hn1 : 1 ≤ n) (hnw : n ≤ w) (hn21 : n < 2 ^ 21)
    (hnb : ∀ t : State, Scr t B Z → t.gpr .x0 = B → t.gpr .x12 = BitVec.ofNat 64 w →
      t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) → t.mem = s.mem →
      WP isa (.block nb) t fun t' => (t'.gpr .x12 = BitVec.ofNat 64 n ∧ t'.mem = t.mem ∧ t'.v = t.v) ∧
        Keep [.x3, .x4, .x5, .x6, .x7, .x12] t t')
    (hUn : wv s.mem B (slot w iU) w < 2 ^ (64 * n)) (hMn : wv s.mem B (slot w iM) w < 2 ^ (64 * n))
    (hVM : wv s.mem B (slot w iV) w = wv s.mem B (slot w iM) w) :
    WP isa (inverseAt nb iU iV iX₁ iX₂ iM iT) s fun t =>
      t.gpr .x0 = B ∧ Frm B [ar w iU, ar w iV, ar w iX₁, ar w iX₂, ar w iT] s.mem t.mem ∧
      Keep (.x11 :: .x12 :: stepRegs) s t ∧
      (wv s.mem B (slot w iM) w % 2 = 1 → 1 < wv s.mem B (slot w iM) w →
        wv t.mem B (slot w iV) w = Nat.gcd (wv s.mem B (slot w iU) w) (wv s.mem B (slot w iM) w) ∧
        ((wv s.mem B (slot w iM) w : Nat) : Int) ∣
          (wv t.mem B (slot w iX₂) w : Int) * wv s.mem B (slot w iU) w - wv t.mem B (slot w iV) w ∧
        wv t.mem B (slot w iX₂) w < wv s.mem B (slot w iM) w) := by
  have hs := h.scr
  have hn' := hs.nowrap
  have hw := h.w2
  have hZ := h.hZ
  have sl : ∀ j < 16, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_lt (w := w) hj) hZ
  unfold inverseAt
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨⟨h12₁, h11₁, m₁, _⟩, k₁⟩ =>
    WP.mono (hnb s₁ (hs.congr k₁.wr) ((k₁.gpr .x0 (by decide)).trans h.x0) h12₁ h11₁ m₁)
      fun s₂ ⟨⟨h12₂, m₂, _⟩, k₂⟩ => ?_))
  have k12 := k₁.trans k₂
  have hm₂ : s₂.mem = s.mem := by rw [m₂, m₁]
  have low : ∀ {j : Nat}, wv s.mem B (slot w j) w < 2 ^ (64 * n) →
      wv s₂.mem B (slot w j) n = wv s.mem B (slot w j) w := fun hj => by
    rw [hm₂, wv_low_mod _ _ hnw, Nat.mod_eq_of_lt hj]
  have VMn : wv s₂.mem B (slot w iV) n = wv s₂.mem B (slot w iM) n := by
    rw [low (by rw [hVM]; exact hMn), low hMn, hVM]
  rw [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [tailZ]) (WP.mono (inverseB_ok (hs.congr k12.wr)
    ((k12.gpr .x0 (by decide)).trans h.x0) ((k₂.gpr .x11 (by decide)).trans h11₁) h12₂ hn1 hnw hw hn21 hZ
    hU hV hX₁ hX₂ hM hT dUV dUX₁ dUX₂ dUM dUT dVX₁ dVX₂ dVM dVT dX dX₁M dX₁T dX₂M dX₂T dMT VMn)
    fun s₃ ⟨sc₃, t0, t1, t2, t11, t12, fr₃, k₃, val⟩ => ?_)
  refine wp_seqs_append (by simp [tailZ]) (by simp [tailZ]) (WP.mono (tailZ_ok sc₃ t0 t11 t12 hnw hw hZ hV)
    fun s₄ ⟨eV, oV, vV, k₄⟩ => ?_)
  have k₄' := k₄
  refine WP.mono (tailZ_ok (sc₃.congr k₄.wr) ((k₄.gpr .x0 (by decide)).trans t0)
    ((k₄.gpr .x11 (by decide)).trans t11) ((k₄.gpr .x12 (by decide)).trans t12) hnw hw hZ hX₂)
    fun t ⟨eX, oX, vX, k₅⟩ => ⟨(k₅.gpr .x0 (by decide)).trans ((k₄.gpr .x0 (by decide)).trans t0), ?_, ?_, ?_⟩
  · have f4 : Frm B [ar w iU, ar w iV, ar w iX₁, ar w iX₂, ar w iT] s₃.mem s₄.mem :=
      Frm.of_outside oV (by simp [ar])
    have f5 : Frm B [ar w iU, ar w iV, ar w iX₁, ar w iX₂, ar w iT] s₄.mem t.mem :=
      Frm.of_outside oX (by simp [ar])
    rw [← hm₂]
    exact (fr₃.trans f4).trans f5
  · have k := (k12.trans k₃).trans (k₄.trans k₅)
    exact keep_restore (k.mono (by decide))
      (by rw [k₅.gpr .x1 (by decide), k₄.gpr .x1 (by decide), t1, k12.gpr .x1 (by decide)])
      (by rw [k₅.gpr .x2 (by decide), k₄.gpr .x2 (by decide), t2, k12.gpr .x2 (by decide)])
  · intro h1 h2
    rw [← low hMn] at h1 h2
    obtain ⟨v1, v2, v3⟩ := val h1 h2
    have sVX := slot_apart (w := w) (a := 8 * w) (b := 8 * (w + 2)) dVX₂ (by omega_arith) (by omega_arith)
    have sXV := slot_apart (w := w) (a := 8 * n) (b := 8 * (w + 2)) dVX₂.symm (by omega_arith) (by omega_arith)
    have Vt : wv t.mem B (slot w iV) w = wv s₃.mem B (slot w iV) n := by
      rw [← eV, oX.wv (by rcases sVX with h | h <;> omega_arith) (by have := sl _ hV; omega_arith)]
    have Xt : wv t.mem B (slot w iX₂) w = wv s₃.mem B (slot w iX₂) n := by
      rw [eX, oV.wv (by rcases sXV with h | h <;> omega_arith) (by have := sl _ hX₂; omega_arith)]
    simp only [low hMn, low hUn] at v1 v2 v3
    rw [Vt, Xt, v1, Nat.gcd_comm]
    exact ⟨rfl, by rw [Nat.gcd_comm] at v2; exact v2, v3⟩

/-- `inverseAtS nb`: `inverseAt_ok` with `x₂ 2^(5 (3 n + 2))` the inverse. -/
theorem inverseAtS_ok {s : State} {B : Addr} {Z w n : Nat} {nb : List Instr} {iU iV iX₁ iX₂ iM iT : Nat}
    (h : Ws s B Z w)
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dUV : iU ≠ iV) (dUX₁ : iU ≠ iX₁) (dUX₂ : iU ≠ iX₂) (dUM : iU ≠ iM) (dUT : iU ≠ iT) (dVX₁ : iV ≠ iX₁)
    (dVX₂ : iV ≠ iX₂) (dVM : iV ≠ iM) (dVT : iV ≠ iT) (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT)
    (dX₂M : iX₂ ≠ iM) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT) (hn1 : 1 ≤ n) (hnw : n ≤ w) (hn21 : n < 2 ^ 21)
    (hnb : ∀ t : State, Scr t B Z → t.gpr .x0 = B → t.gpr .x12 = BitVec.ofNat 64 w →
      t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) → t.mem = s.mem →
      WP isa (.block nb) t fun t' => (t'.gpr .x12 = BitVec.ofNat 64 n ∧ t'.mem = t.mem ∧ t'.v = t.v) ∧
        Keep [.x3, .x4, .x5, .x6, .x7, .x12] t t')
    (hUn : wv s.mem B (slot w iU) w < 2 ^ (64 * n)) (hMn : wv s.mem B (slot w iM) w < 2 ^ (64 * n))
    (hVM : wv s.mem B (slot w iV) w = wv s.mem B (slot w iM) w) :
    WP isa (inverseAtS nb iU iV iX₁ iX₂ iM iT) s fun t =>
      t.gpr .x0 = B ∧ Frm B [ar w iU, ar w iV, ar w iX₁, ar w iX₂, ar w iT] s.mem t.mem ∧
      Keep (.x11 :: .x12 :: stepRegs) s t ∧
      (wv s.mem B (slot w iM) w % 2 = 1 → 1 < wv s.mem B (slot w iM) w →
        wv t.mem B (slot w iV) w = Nat.gcd (wv s.mem B (slot w iU) w) (wv s.mem B (slot w iM) w) ∧
        ((wv s.mem B (slot w iM) w : Nat) : Int) ∣
          (wv t.mem B (slot w iX₂) w : Int) * 2 ^ (5 * (3 * n + 2)) * wv s.mem B (slot w iU) w -
            wv t.mem B (slot w iV) w ∧
        wv t.mem B (slot w iX₂) w < wv s.mem B (slot w iM) w) := by
  have hs := h.scr
  have hn' := hs.nowrap
  have hw := h.w2
  have hZ := h.hZ
  have sl : ∀ j < 16, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_lt (w := w) hj) hZ
  unfold inverseAtS
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨⟨h12₁, h11₁, m₁, _⟩, k₁⟩ =>
    WP.mono (hnb s₁ (hs.congr k₁.wr) ((k₁.gpr .x0 (by decide)).trans h.x0) h12₁ h11₁ m₁)
      fun s₂ ⟨⟨h12₂, m₂, _⟩, k₂⟩ => ?_))
  have k12 := k₁.trans k₂
  have hm₂ : s₂.mem = s.mem := by rw [m₂, m₁]
  have low : ∀ {j : Nat}, wv s.mem B (slot w j) w < 2 ^ (64 * n) →
      wv s₂.mem B (slot w j) n = wv s.mem B (slot w j) w := fun hj => by
    rw [hm₂, wv_low_mod _ _ hnw, Nat.mod_eq_of_lt hj]
  have VMn : wv s₂.mem B (slot w iV) n = wv s₂.mem B (slot w iM) n := by
    rw [low (by rw [hVM]; exact hMn), low hMn, hVM]
  rw [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [tailZ]) (WP.mono (inverseBS_ok (hs.congr k12.wr)
    ((k12.gpr .x0 (by decide)).trans h.x0) ((k₂.gpr .x11 (by decide)).trans h11₁) h12₂ hn1 hnw hw hn21 hZ
    hU hV hX₁ hX₂ hM hT dUV dUX₁ dUX₂ dUM dUT dVX₁ dVX₂ dVM dVT dX dX₁M dX₁T dX₂M dX₂T dMT VMn)
    fun s₃ ⟨sc₃, t0, t1, t2, t11, t12, fr₃, k₃, val⟩ => ?_)
  refine wp_seqs_append (by simp [tailZ]) (by simp [tailZ]) (WP.mono (tailZ_ok sc₃ t0 t11 t12 hnw hw hZ hV)
    fun s₄ ⟨eV, oV, vV, k₄⟩ => ?_)
  have k₄' := k₄
  refine WP.mono (tailZ_ok (sc₃.congr k₄.wr) ((k₄.gpr .x0 (by decide)).trans t0)
    ((k₄.gpr .x11 (by decide)).trans t11) ((k₄.gpr .x12 (by decide)).trans t12) hnw hw hZ hX₂)
    fun t ⟨eX, oX, vX, k₅⟩ => ⟨(k₅.gpr .x0 (by decide)).trans ((k₄.gpr .x0 (by decide)).trans t0), ?_, ?_, ?_⟩
  · have f4 : Frm B [ar w iU, ar w iV, ar w iX₁, ar w iX₂, ar w iT] s₃.mem s₄.mem :=
      Frm.of_outside oV (by simp [ar])
    have f5 : Frm B [ar w iU, ar w iV, ar w iX₁, ar w iX₂, ar w iT] s₄.mem t.mem :=
      Frm.of_outside oX (by simp [ar])
    rw [← hm₂]
    exact (fr₃.trans f4).trans f5
  · have k := (k12.trans k₃).trans (k₄.trans k₅)
    exact keep_restore (k.mono (by decide))
      (by rw [k₅.gpr .x1 (by decide), k₄.gpr .x1 (by decide), t1, k12.gpr .x1 (by decide)])
      (by rw [k₅.gpr .x2 (by decide), k₄.gpr .x2 (by decide), t2, k12.gpr .x2 (by decide)])
  · intro h1 h2
    rw [← low hMn] at h1 h2
    obtain ⟨v1, v2, v3⟩ := val h1 h2
    have sVX := slot_apart (w := w) (a := 8 * w) (b := 8 * (w + 2)) dVX₂ (by omega_arith) (by omega_arith)
    have sXV := slot_apart (w := w) (a := 8 * n) (b := 8 * (w + 2)) dVX₂.symm (by omega_arith) (by omega_arith)
    have Vt : wv t.mem B (slot w iV) w = wv s₃.mem B (slot w iV) n := by
      rw [← eV, oX.wv (by rcases sVX with h | h <;> omega_arith) (by have := sl _ hV; omega_arith)]
    have Xt : wv t.mem B (slot w iX₂) w = wv s₃.mem B (slot w iX₂) n := by
      rw [eX, oV.wv (by rcases sXV with h | h <;> omega_arith) (by have := sl _ hX₂; omega_arith)]
    simp only [low hMn, low hUn] at v1 v2 v3
    rw [Vt, Xt, v1, Nat.gcd_comm]
    exact ⟨rfl, by rw [Nat.gcd_comm] at v2; exact v2, v3⟩

instance invLaw : InvLaw where
  inverse_ok := inverse_ok
  inverseAt_ok := inverseAt_ok
  inverseAtS_ok := inverseAtS_ok

end VG.Proof.Rsa.AArch64
