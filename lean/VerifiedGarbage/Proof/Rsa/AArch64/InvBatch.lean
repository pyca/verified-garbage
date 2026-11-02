module

public import VerifiedGarbage.Proof.Divstep.SignedWords
public import VerifiedGarbage.Proof.Divstep.Alg
public import VerifiedGarbage.Proof.Divstep.TcS
public import VerifiedGarbage.Proof.Divstep.BatchBasic
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Impl.Rsa.AArch64.Keys
public import VerifiedGarbage.Proof.Bignum.Layout
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
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
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
# One word of Montgomery reduction on signed multiword numbers

`mredRaw p m t` (`Proof/Divstep/Alg.lean`) as code computes it on `t`, a
signed number of `L` words: sign-extended to `L + 1` words, `k p` added for
`k = t₀ m mod 2^64` modulo `2^(64 (L + 1))`, and the words above the lowest
kept (`mredSext_words`). Signed numbers modulo `2^(64 L)` (`sgn_emod`,
`sgn_of_emod`).
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
  · exact Int.emod_eq_of_lt (by omega) (by omega)
  · rw [show (x : Int) - 2 * H = x + (-1) * (2 * H) by omega, Int.add_mul_emod_self_right]
    exact Int.emod_eq_of_lt (by omega) (by omega)

/-- The signed number of `L` words congruent to `y`, if `y` fits. -/
theorem sgn_of_emod {L x : Nat} {y : Int} (hL : 1 ≤ L)
    (hy₀ : -2 ^ (64 * L - 1) ≤ y) (hy₁ : y < 2 ^ (64 * L - 1)) (h : (x : Int) = y % 2 ^ (64 * L)) :
    sgn L x = y := by
  obtain ⟨H, h63, e1, e2, e3, e4⟩ := pow_H hL
  unfold sgn
  simp only [e1, e4]; rw [e3] at hy₀ hy₁; rw [e4] at h
  by_cases hy : 0 ≤ y
  · rw [Int.emod_eq_of_lt hy (by omega)] at h
    rw [ite_eq_left (by omega : x < H)]; exact h
  · rw [show y = (y + 2 * H) + (-1) * (2 * H) by omega, Int.add_mul_emod_self_right,
      Int.emod_eq_of_lt (by omega) (by omega)] at h
    rw [ite_eq_right (by omega : ¬ x < H)]; omega

/-- Sign extension by a word: the top word's sign mask. -/
theorem sext_emod {L S : Nat} (hL : 1 ≤ L) :
    ((S + 2 ^ (64 * L) * (if S < 2 ^ (64 * L - 1) then 0 else 2 ^ 64 - 1) : Nat) : Int) =
      sgn L S + (if S < 2 ^ (64 * L - 1) then 0 else 2 ^ (64 * (L + 1))) := by
  obtain ⟨e, h63⟩ := pow_half hL
  have e2 : (2 : Int) ^ (64 * (L + 1)) = 2 ^ (64 * L) * 2 ^ 64 := by rw [Nat.mul_succ, Int.pow_add]
  unfold sgn
  rw [e2]
  split
  · simp
  · push_cast; grind

/-- One word of Montgomery reduction of the signed `L`-word `S` as the code
computes it: `W₁` the sign extension, `k = S₀ m mod 2^64`, `W₂ = W₁ + k p`
modulo `2^(64 (L + 1))`, and `O` its words above the lowest. -/
theorem mredSext_words {L S W₂ O : Nat} {k p m : Int} (hL : 1 ≤ L)
    (hm : (p * m + 1) % 2 ^ 64 = 0) (hk : k = (S % 2 ^ 64 : Nat) * m % 2 ^ 64)
    (hW₂ : (W₂ : Int) = ((S + 2 ^ (64 * L) * (if S < 2 ^ (64 * L - 1) then 0 else 2 ^ 64 - 1) : Nat) + k * p) %
      2 ^ (64 * (L + 1)))
    (hO : W₂ = W₂ % 2 ^ 64 + 2 ^ 64 * O) :
    (O : Int) = mredRaw p m (sgn L S) % 2 ^ (64 * L) := by
  obtain ⟨H, h63, e1, e2, e3, e4⟩ := pow_H hL
  have eQP : (2 : Int) ^ (64 * (L + 1)) = 2 ^ 64 * 2 ^ (64 * L) := by
    rw [Nat.mul_succ, Int.pow_add, Int.mul_comm]
  have eP : (2 : Int) ^ (64 * L) = 2 ^ (64 * L - 64) * 2 ^ 64 := by rw [← Int.pow_add]; congr 1; omega
  set tv := sgn L S with htv
  -- `S ≡ tv` modulo `2^64`.
  have hS64 : ((S % 2 ^ 64 : Nat) : Int) % 2 ^ 64 = tv % 2 ^ 64 := by
    rw [htv, Int.natCast_mod, show ((2 ^ 64 : Nat) : Int) = 2 ^ 64 by rfl, Int.emod_emod]; unfold sgn
    split
    · rfl
    · rw [eP, show (S : Int) - 2 ^ (64 * L - 64) * 2 ^ 64 = S + (-2 ^ (64 * L - 64)) * 2 ^ 64 by grind,
        Int.add_mul_emod_self_right]
  have hk' : k = tv * m % 2 ^ 64 := by
    rw [hk, Int.mul_emod, hS64, ← Int.mul_emod]
  -- `2^64` divides `tv + k p`.
  have hdvd : (2 : Int) ^ 64 ∣ tv + k * p := by
    have h1 : (2 : Int) ^ 64 ∣ tv * (p * m + 1) := Int.dvd_mul_of_dvd_right (Int.dvd_of_emod_eq_zero hm)
    have h2 : (2 : Int) ^ 64 ∣ tv * m - k := by
      rw [hk']; exact Int.dvd_self_sub_emod
    have := Int.dvd_sub h1 (Int.dvd_mul_of_dvd_left (c := p) h2)
    rw [show tv * (p * m + 1) - (tv * m - k) * p = tv + k * p by grind] at this
    exact this
  obtain ⟨R, hR⟩ := hdvd
  have hW : (W₂ : Int) = 2 ^ 64 * (R % 2 ^ (64 * L)) := by
    rw [hW₂, sext_emod hL]
    rw [show sgn L S + (if S < 2 ^ (64 * L - 1) then 0 else (2 : Int) ^ (64 * (L + 1))) + k * p =
      (tv + k * p) + (if S < 2 ^ (64 * L - 1) then 0 else 1) * 2 ^ (64 * (L + 1)) by split <;> grind,
      Int.add_mul_emod_self_right, hR, eQP, Int.mul_emod_mul_of_pos _ _ (by decide)]
  have hmr : mredRaw p m tv = R := by
    unfold mredRaw; rw [← hk', hR, Int.mul_ediv_cancel_left _ (by decide)]
  rw [hmr]
  have h0 : (W₂ % 2 ^ 64 : Nat) = 0 := by
    have : (W₂ : Int) % 2 ^ 64 = 0 := by rw [hW]; exact Int.mul_emod_right _ _
    omega
  rw [h0, Nat.zero_add] at hO
  have : (W₂ : Int) = 2 ^ 64 * O := by rw [hO]; push_cast; rfl
  rw [hW] at this
  exact (Int.eq_of_mul_eq_mul_left (by decide) this).symm

/-- A linear combination's words, from unsigned words and a carry, as a
signed number, if it fits. -/
theorem lin_sgn {L W F G : Nat} {u v c : Int} (hL : 1 ≤ L) (hW : W < 2 ^ (64 * L)) (hF : F < 2 ^ (64 * L))
    (hG : G < 2 ^ (64 * L)) (h : (W : Int) + 2 ^ (64 * L) * c = u * F + v * G)
    (r₀ : -2 ^ (64 * L - 1) ≤ u * sgn L F + v * sgn L G) (r₁ : u * sgn L F + v * sgn L G < 2 ^ (64 * L - 1)) :
    sgn L W = u * sgn L F + v * sgn L G := by
  refine sgn_of_emod hL r₀ r₁ ?_
  have eF := Int.emod_add_mul_ediv (sgn L F) (2 ^ (64 * L))
  have eG := Int.emod_add_mul_ediv (sgn L G) (2 ^ (64 * L))
  rw [sgn_emod hL hF] at eF; rw [sgn_emod hL hG] at eG
  have hP : (0 : Int) < 2 ^ (64 * L) := Int.pow_pos (by decide)
  rw [show u * sgn L F + v * sgn L G = W + (2 ^ (64 * L)) * (c + u * (sgn L F / 2 ^ (64 * L)) +
    v * (sgn L G / 2 ^ (64 * L))) by rw [← eF, ← eG] at *; grind, Int.add_mul_emod_self_left,
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast hW)]

/-- A signed number's low word. -/
theorem sgn_mod64 {L F : Nat} (hL : 1 ≤ L) (hF : F < 2 ^ (64 * L)) : sgn L F % 2 ^ 64 = ((F % 2 ^ 64 : Nat) : Int) := by
  have e := Int.emod_add_mul_ediv (sgn L F) (2 ^ (64 * L))
  rw [sgn_emod hL hF] at e
  have hd : (2 : Int) ^ 64 ∣ 2 ^ (64 * L) := ⟨2 ^ (64 * L - 64), by rw [← Int.pow_add]; congr 1; omega⟩
  rw [← e, Int.add_emod, Int.emod_eq_zero_of_dvd (Int.dvd_mul_of_dvd_left hd), Int.add_zero, Int.emod_emod]
  rfl

/-- A word's signed value is a small integer's. -/
theorem toInt_ofInt64 {u : Int} (h0 : -2 ^ 63 ≤ u) (h1 : u < 2 ^ 63) : (BitVec.ofInt 64 u).toInt = u := by
  rw [BitVec.toInt_ofInt]; exact Int.bmod_eq_of_le (by omega) (by omega)


/-! ## Negating and correcting signed numbers -/

/-- The sign of a number of `n + 1` words is its top word's top bit. -/
theorem sgn_neg_iff {n W s : Nat} (hW : W < 2 ^ (64 * n)) (hs : s < 2 ^ 64) :
    sgn (n + 1) (W + 2 ^ (64 * n) * s) < 0 ↔ 2 ^ 63 ≤ s := by
  have t := top_sign hW hs
  unfold sgn
  have hR : W + 2 ^ (64 * n) * s < 2 ^ (64 * (n + 1)) := by
    have : 2 ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by
      rw [← Nat.pow_add, show 64 * n + 64 = 64 * (n + 1) by omega]
    have := Nat.mul_le_mul_left (2 ^ (64 * n)) (show s + 1 ≤ 2 ^ 64 by omega)
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  split
  · rename_i h; exact ⟨fun h' => by omega, fun h' => absurd (t.mp h) (by omega)⟩
  · rename_i h
    refine ⟨fun _ => Nat.le_of_not_lt fun h' => h (t.mpr h'), fun _ => ?_⟩
    have : ((W + 2 ^ (64 * n) * s : Nat) : Int) < 2 ^ (64 * (n + 1)) := by exact_mod_cast hR
    omega

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
      · have := Nat.mul_le_mul_left (2 * H) hc; omega
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
            · have : c = 0 := by omega
              subst this; omega
            · omega
          · have := Nat.mul_le_mul_left (2 * H) hc; omega
        subst hc
        have : Y = 0 := by omega
        subst this
        rw [ite_eq_left (show (0 : Nat) < H by omega)]; simp
      · have hc : c = 0 := by
          rcases Nat.eq_zero_or_pos c with hc | hc
          · exact hc
          · have := Nat.mul_le_mul_left (2 * H) hc; omega
        subst hc
        rw [ite_eq_right (by omega : ¬ Y < H)]
        push_cast
        omega
    · rw [ite_eq_right hx] at hr ⊢
      have hc : c = 0 := by
        rcases Nat.eq_zero_or_pos c with hc | hc
        · exact hc
        · have := Nat.mul_le_mul_left (2 * H) hc; omega
      subst hc
      rw [ite_eq_left (by omega : Y < H)]
      push_cast at hr ⊢
      omega

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
    (by rw [abs_of_nonneg hp0]; omega) (by rw [abs_of_nonneg hx]; omega) (59 * k)
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

section
variable {s : State}

theorem exec_sbc_x {d n m : Reg} :
    exec (.sbc .x d n m) s = some (s.write .x d (s.gpr n + ~~~s.gpr m + BitVec.ofNat 64 s.c.toNat)) := rfl

theorem exec_umov_x {d : Reg} {n : VReg} {i : Nat} (h : i < 2) :
    exec (.umov .x d n i) s = some (s.write .x d ((s.v n).extractLsb' (64 * i) 64)) := by
  simp only [exec, Size.bits, show i * 64 < 128 by omega, ite_true]


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

open VG.Impl.Rsa.AArch64.Keys

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
open VG.Proof.Bignum in
/-- Arrays `j ≠ k` of `w + 2` words: any parts of them are apart. -/
theorem slot_apart {w j k a b : Nat} (h : j ≠ k) (ha : a ≤ 8 * (w + 2)) (hb : b ≤ 8 * (w + 2)) :
    slot w j + a ≤ slot w k ∨ slot w k + b ≤ slot w j := by
  rcases slot_sep (w := w) h with h' | h' <;> [exact .inl (by omega); exact .inr (by omega)]

end VG.Proof.Rsa.AArch64

-- From `Proof/Rsa/AArch64/InvRow.lean`.
/-!
# RSA private keys on AArch64: the batched inverse's linear combinations

`rowP cv x y o`: `[o] := u [x] + v [y]` modulo `2^(64 (n + 1))`, `u` and `v`
the signed lanes of `cv` (`rowP_ok`), by `rowBody` a word at a time
(`rowWord_ok`, `Divstep.rowWord`), its invariant `LinInv`: the words stored
and the signed carry hold `u X + v Y` for the words read (`linStep_ok`).
`[o]` may be `[y]` (or `[x]`): each word is read before it is written.
-/


namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.InvBatch
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- A word of `rowBody`: `x4 [x16] + x5 [x17] + x13`, its low word stored at
`x8` and its high word the next carry. -/
theorem rowWord_ok (s : State) {B : Addr} {Z eX eY eO : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eX) (h17 : s.gpr .x17 = off B eY) (h8 : s.gpr .x8 = off B eO)
    (h9 : s.gpr .x9 = 0#64 - (s.gpr .x4 >>> 63)) (h10 : s.gpr .x10 = 0#64 - (s.gpr .x5 >>> 63))
    (hX : eX + 8 ≤ Z) (hY : eY + 8 ≤ Z) (hO : eO + 8 ≤ Z)
    (hb : (s.gpr .x4).toInt.natAbs + (s.gpr .x5).toInt.natAbs ≤ 2 ^ 62) (hc : (s.gpr .x13).toInt.natAbs ≤ 2 ^ 62) :
    WP isa (.block rowBody) s fun t => ∃ lo : BitVec 64, t.mem = s.mem.writeW (off B eO) lo ∧
      (lo.toNat : Int) + 2 ^ 64 * (t.gpr .x13).toInt = (s.gpr .x4).toInt * (word s.mem B eX).toNat +
        (s.gpr .x5).toInt * (word s.mem B eY).toNat + (s.gpr .x13).toInt ∧ (t.gpr .x13).toInt.natAbs ≤ 2 ^ 62 ∧
      t.gpr .x16 = off B (eX + 8) ∧ t.gpr .x17 = off B (eY + 8) ∧ t.gpr .x8 = off B (eO + 8) := by
  unfold rowBody
  brun [h16, h17, h8, h9, h10, hs.ld hX, hs.ld hY, hs.st hO, exec_sbc_x]
  refine ⟨_, rfl, ?_⟩
  have := Divstep.rowWord (s.gpr .x4) (s.gpr .x5) (word s.mem B eX) (word s.mem B eY) (s.gpr .x13) hb hc
  simp only [Bool.toNat_false, BitVec.add_zero, Nat.add_zero, word] at this ⊢
  exact this

/-- After `j` words of `rowBody`. -/
structure LinInv (s₀ : State) (B : Addr) (Z eX eY eO : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x1, .x2, .x3, .x6, .x7, .x8, .x13, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eX + 8 * j)
  x17 : t.gpr .x17 = off B (eY + 8 * j)
  x8 : t.gpr .x8 = off B (eO + 8 * j)
  out : Outside B eO (8 * j) s₀.mem t.mem
  val : (wv t.mem B eO j : Int) + 2 ^ (64 * j) * (t.gpr .x13).toInt =
    (s₀.gpr .x4).toInt * wv s₀.mem B eX j + (s₀.gpr .x5).toInt * wv s₀.mem B eY j + (s₀.gpr .x13).toInt
  cb : (t.gpr .x13).toInt.natAbs ≤ 2 ^ 62

theorem linStep_ok {s₀ : State} {B : Addr} {Z L eX eY eO : Nat}
    (h9 : s₀.gpr .x9 = 0#64 - (s₀.gpr .x4 >>> 63)) (h10 : s₀.gpr .x10 = 0#64 - (s₀.gpr .x5 >>> 63))
    (hb : (s₀.gpr .x4).toInt.natAbs + (s₀.gpr .x5).toInt.natAbs ≤ 2 ^ 62)
    (hX : eX + 8 * L ≤ Z) (hY : eY + 8 * L ≤ Z) (hO : eO + 8 * L ≤ Z)
    (sX : eO ≤ eX ∨ eX + 8 * L ≤ eO) (sY : eO ≤ eY ∨ eY + 8 * L ≤ eO)
    {j : Nat} (hj : j < L) {t : State} (hI : LinInv s₀ B Z eX eY eO j t) :
    WP isa (.block (rowBody ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      LinInv s₀ B Z eX eY eO (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have k4 : t.gpr .x4 = s₀.gpr .x4 := hI.keep.gpr .x4 (by decide)
  have k5 : t.gpr .x5 = s₀.gpr .x5 := hI.keep.gpr .x5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x1, .x2, .x3, .x6, .x7, .x8, .x13, .x16, .x17] (rowWord_ok t hI.scr hI.x16 hI.x17 hI.x8
    (by rw [hI.keep.gpr .x9 (by decide), k4, h9]) (by rw [hI.keep.gpr .x10 (by decide), k5, h10])
    (by omega) (by omega) (by omega) (by rw [k4, k5]; exact hb) hI.cb)
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨lo, hm, hv, hcb, h16, h17, h8⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', _⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have hmem : t'.mem = t.mem.writeW (off B (eO + 8 * j)) lo := hm'.trans hm
  have hx : word t.mem B (eX + 8 * j) = word s₀.mem B (eX + 8 * j) :=
    hI.out.word (by omega) (by omega)
  have hy : word t.mem B (eY + 8 * j) = word s₀.mem B (eY + 8 * j) :=
    hI.out.word (by omega) (by omega)
  have e13 : t'.gpr .x13 = t₁.gpr .x13 := k'.gpr .x13 (by decide)
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x8 (by decide), h8, Nat.mul_succ, Nat.add_assoc], ?_, ?_, by rw [e13]; exact hcb⟩
  · rw [hmem]
    refine fun x hx' => ?_
    rw [writeW_outside t.mem B lo (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hmem, wv_writeW_top _ _ _ _ _ (by omega), e13]
    simp only [wv]
    rw [hx, hy, k4, k5] at hv
    have hval := hI.val
    have e : (2 : Int) ^ (64 * (j + 1)) = 2 ^ (64 * j) * 2 ^ 64 := by rw [Nat.mul_succ, Int.pow_add]
    rw [e]
    push_cast
    have hv' := congrArg (fun z => (2 : Int) ^ (64 * j) * z) hv
    simp only [Int.mul_add] at hv'
    grind

/-- `rowBody`'s loop over `L` words, from the carry `x13 = 0`. -/
theorem linLoop_ok {s : State} {B : Addr} {Z L eX eY eO : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eX) (h17 : s.gpr .x17 = off B eY) (h8 : s.gpr .x8 = off B eO)
    (h9 : s.gpr .x9 = 0#64 - (s.gpr .x4 >>> 63)) (h10 : s.gpr .x10 = 0#64 - (s.gpr .x5 >>> 63))
    (h13 : s.gpr .x13 = 0) (h14 : s.gpr .x14 = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hL' : L < 2 ^ 32)
    (hb : (s.gpr .x4).toInt.natAbs + (s.gpr .x5).toInt.natAbs ≤ 2 ^ 62)
    (hX : eX + 8 * L ≤ Z) (hY : eY + 8 * L ≤ Z) (hO : eO + 8 * L ≤ Z)
    (sX : eO ≤ eX ∨ eX + 8 * L ≤ eO) (sY : eO ≤ eY ∨ eY + 8 * L ≤ eO) :
    WP isa (countLoop .x14 rowBody) s (LinInv s B Z eX eY eO L) := by
  have hn := hs.nowrap
  have h0 : LinInv s B Z eX eY eO 0 s :=
    ⟨hs, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, by rw [h8]; rfl, Outside.refl _ _ _ _,
      by simp [wv], by rw [h13]; decide⟩
  exact wp_countdown (N := L) (by omega) (by omega) (LinInv s B Z eX eY eO)
    (fun j hj t hI _ => linStep_ok h9 h10 hb hX hY hO sX sY hj hI) h0 h14

/-- `rowP`'s start: the coefficients from `cv` and their sign masks. -/
theorem rowHead_ok (s : State) {cv : VReg} (hcv : cv = .v16 ∨ cv = .v17) :
    WP isa (.block (([.umov .x .x4 cv 0, .umov .x .x5 cv 1] : List Instr) ++ coefMasks)) s fun t =>
      (t.gpr .x4 = (s.v cv).extractLsb' 0 64 ∧ t.gpr .x5 = (s.v cv).extractLsb' 64 64 ∧
        t.gpr .x9 = 0#64 - (t.gpr .x4 >>> 63) ∧ t.gpr .x10 = 0#64 - (t.gpr .x5 >>> 63) ∧ t.mem = s.mem ∧
        t.v = s.v) ∧ Keep [.x4, .x5, .x9, .x10, .x13] s t := by
  rcases hcv with rfl | rfl <;>
  · refine WP.keep [.x4, .x5, .x9, .x10, .x13] ?_ (by decide) (by decide) (by decide +kernel)
    unfold coefMasks
    brun [exec_umov_x, RegUpd.v_write, Nat.mul_zero, Nat.mul_one, show BitVec.setWidth 64 0#16 = 0#64 from rfl]

/-- `rowP cv x y o`: `[o] := u [x] + v [y]` modulo `2^(64 (n + 1))`, for the
signed lanes `u`, `v` of `cv`. -/
theorem rowP_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {cv : VReg} (hcv : cv = .v16 ∨ cv = .v17)
    {iX iY iO : Nat} (hX : iX < 16) (hY : iY < 16) (hO : iO < 16)
    (hb : ((s.v cv).extractLsb' 0 64).toInt.natAbs + ((s.v cv).extractLsb' 64 64).toInt.natAbs ≤ 2 ^ 62) :
    WP isa (rowP cv iX iY iO) s fun t => ∃ c : Int,
      (wv t.mem B (slot w iO) (n + 1) : Int) + 2 ^ (64 * (n + 1)) * c =
        ((s.v cv).extractLsb' 0 64).toInt * wv s.mem B (slot w iX) (n + 1) +
        ((s.v cv).extractLsb' 64 64).toInt * wv s.mem B (slot w iY) (n + 1) ∧
      Outside B (slot w iO) (8 * (n + 1)) s.mem t.mem ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x13, .x14, .x16, .x17] s t ∧ t.v = s.v := by
  have hn' := hs.nowrap
  have sl : ∀ j < 16, slot w j + 8 * (w + 2) ≤ Z := fun j hj =>
    Nat.le_trans (slot_lt (w := w) hj) hZ
  have sep : ∀ j k, slot w j ≤ slot w k ∨ slot w k + 8 * (n + 1) ≤ slot w j := fun j k => by
    by_cases h : j = k
    · subst h; exact .inl (Nat.le_refl _)
    · rcases slot_sep (w := w) h with h' | h' <;> [exact .inl (by omega); exact .inr (by omega)]
  have hvn : (rowP cv iX iY iO).allInstrs (fun i => (vdstOf i).isNone) = true := by
    rcases hcv with rfl | rfl <;>
    · simp only [rowP, Code.allInstrs_eq, instrs, List.all_append, base_vnone]; decide
  suffices h : WP isa (rowP cv iX iY iO) s fun t => ∃ c : Int,
      (wv t.mem B (slot w iO) (n + 1) : Int) + 2 ^ (64 * (n + 1)) * c =
        ((s.v cv).extractLsb' 0 64).toInt * wv s.mem B (slot w iX) (n + 1) +
        ((s.v cv).extractLsb' 64 64).toInt * wv s.mem B (slot w iY) (n + 1) ∧
      Outside B (slot w iO) (8 * (n + 1)) s.mem t.mem ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x13, .x14, .x16, .x17] s t from
    WP.mono (WP.vfix h hvn) fun t ⟨⟨c, e, o, k⟩, v⟩ => ⟨c, e, o, k, v⟩
  unfold rowP
  rw [show ([Instr.umov .x .x4 cv 0, .umov .x .x5 cv 1] ++ coefMasks ++ base iX .x16 ++ base iY .x17 ++
      base iO .x8 ++ ([cntL, movi .x13 0] : List Instr)) = ([Instr.umov .x .x4 cv 0, .umov .x .x5 cv 1] ++ coefMasks) ++
      (base iX .x16 ++ base iY .x17 ++ base iO .x8) ++ ([cntL, movi .x13 0] : List Instr) by simp]
  refine WP.seq (WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono (rowHead_ok s hcv)
    fun s₁ ⟨⟨h4, h5, h9, h10, m₁, v₁⟩, k₁⟩ => WP.mono (base3_ok iX iY iO .x16 .x17 .x8
      ((k₁.gpr .x0 (by decide)).trans h0) ((k₁.gpr .x11 (by decide)).trans h11))
    fun s₂ ⟨⟨h16, h17, h8, m₂, _⟩, k₂⟩ => WP.mono (WP.keep [.x13, .x14] (Q := fun t =>
      t.gpr .x13 = 0 ∧ t.gpr .x14 = BitVec.ofNat 64 (n + 1) ∧ t.mem = s₂.mem)
      (by brun [((k₁.trans k₂).gpr .x12 (by decide)).trans h12, cntL]; exact BitVec.ofNat_add_ofNat (n := 64) n 1) (by decide) (by decide) (by decide +kernel))
    fun s₃ ⟨⟨h13, h14, m₃⟩, k₃⟩ => ?_)))
  have k23 := k₂.trans k₃
  have e4 : s₃.gpr .x4 = (s.v cv).extractLsb' 0 64 := (k23.gpr .x4 (by decide)).trans h4
  have e5 : s₃.gpr .x5 = (s.v cv).extractLsb' 64 64 := (k23.gpr .x5 (by decide)).trans h5
  have hm : s₃.mem = s.mem := m₃.trans (m₂.trans m₁)
  refine WP.mono (linLoop_ok (hs.congr (k₁.trans k23).wr) ((k₃.gpr .x16 (by decide)).trans h16)
    ((k₃.gpr .x17 (by decide)).trans h17) ((k₃.gpr .x8 (by decide)).trans h8)
    (by rw [k23.gpr .x9 (by decide), h9, k23.gpr .x4 (by decide)])
    (by rw [k23.gpr .x10 (by decide), h10, k23.gpr .x5 (by decide)]) h13 h14 (by omega) (by omega)
    (by rw [e4, e5]; exact hb) (by have := sl iX hX; omega) (by have := sl iY hY; omega)
    (by have := sl iO hO; omega) (sep iO iX) (sep iO iY)) fun t hI => ⟨(t.gpr .x13).toInt, ?_, ?_, ?_⟩
  · have := hI.val
    rw [e4, e5, hm, h13] at this
    simpa using this
  · rw [← hm]; exact hI.out
  · exact ((k₁.trans k23).trans hI.keep).mono (by decide)
end VG.Proof.Rsa.AArch64

-- From `Proof/Rsa/AArch64/InvShr.lean`.
/-!
# RSA private keys on AArch64: the batched inverse's shift by 59

`shrP s o`: `[o] := [s] >> 59` as signed numbers of `n + 1` words
(`shrP_ok`), by `shr59Body` a word at a time (`shrWord_ok`, invariant
`Shr59Inv`: `Divstep.shr_step`) and the top word from the sign
(`shrTop_ok`, `Divstep.shr_final`). `[o]` may be `[s]`.
-/


namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.InvBatch
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- A word of the shift: words `j` and `j + 1` of `[x16]` into word `j` of `[x17]`. -/
theorem shrWord_ok (s : State) {B : Addr} {Z eS eO : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eS) (h17 : s.gpr .x17 = off B eO) (hS : eS + 16 ≤ Z) (hO : eO + 8 ≤ Z) :
    WP isa (.block shr59Body) s fun t => ∃ o : BitVec 64, t.mem = s.mem.writeW (off B eO) o ∧
      o.toNat = (word s.mem B eS).toNat / 2 ^ 59 + 2 ^ 5 * ((word s.mem B (eS + 8)).toNat % 2 ^ 59) ∧
      t.gpr .x16 = off B (eS + 8) ∧ t.gpr .x17 = off B (eO + 8) := by
  unfold shr59Body
  brun [h16, h17, hs.ld (show eS + 8 ≤ Z by omega), hs.ld (show eS + 8 + 8 ≤ Z by omega), hs.st hO, exec_extr_x]
  exact ⟨_, rfl, Divstep.extr59 _ _⟩

/-- The top word of the shift, from the sign. -/
theorem shrTop_ok (s : State) {B : Addr} {Z eS eO : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eS) (h17 : s.gpr .x17 = off B eO) (hS : eS + 8 ≤ Z) (hO : eO + 8 ≤ Z) :
    WP isa (.block shrTop) s fun t => ∃ o : BitVec 64, t.mem = s.mem.writeW (off B eO) o ∧
      o.toNat = (word s.mem B eS).toNat / 2 ^ 59 +
        2 ^ 5 * ((if (word s.mem B eS).toNat < 2 ^ 63 then 0 else 2 ^ 64 - 1) % 2 ^ 59) := by
  unfold shrTop
  brun [h16, h17, hs.ld hS, hs.st hO, exec_extr_x, show BitVec.setWidth 64 0#16 = 0#64 from rfl]
  refine ⟨_, rfl, ?_⟩
  rw [Divstep.extr59, Divstep.signMask_eq]
  split <;> rfl

/-- After `j` words of the shift: the `j + 1` words read are the low 59 bits
of word 0, `2^59` times the `j` words written, and the rest of word `j`. -/
structure Shr59Inv (s₀ : State) (B : Addr) (Z eS eO : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eS + 8 * j)
  x17 : t.gpr .x17 = off B (eO + 8 * j)
  out : Outside B eO (8 * j) s₀.mem t.mem
  val : wv s₀.mem B eS (j + 1) = (word s₀.mem B eS).toNat % 2 ^ 59 + 2 ^ 59 * wv t.mem B eO j +
    2 ^ (64 * j) * 2 ^ 59 * ((word s₀.mem B (eS + 8 * j)).toNat / 2 ^ 59)

theorem shr59Step_ok {s₀ : State} {B : Addr} {Z n eS eO : Nat} (hS : eS + 8 * (n + 1) ≤ Z)
    (hO : eO + 8 * (n + 1) ≤ Z) (sep : eO ≤ eS ∨ eS + 8 * (n + 1) ≤ eO)
    {j : Nat} (hj : j < n) {t : State} (hI : Shr59Inv s₀ B Z eS eO j t) :
    WP isa (.block (shr59Body ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      Shr59Inv s₀ B Z eS eO (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x16, .x17] (shrWord_ok t hI.scr hI.x16 hI.x17 (by omega) (by omega))
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨o, hm, ho, h16, h17⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', _⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have hmem : t'.mem = t.mem.writeW (off B (eO + 8 * j)) o := hm'.trans hm
  have h0 : word t.mem B (eS + 8 * j) = word s₀.mem B (eS + 8 * j) := hI.out.word (by omega) (by omega)
  have h1 : word t.mem B (eS + 8 * j + 8) = word s₀.mem B (eS + 8 * j + 8) := hI.out.word (by omega) (by omega)
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hmem]
    refine fun x hx' => ?_
    rw [writeW_outside t.mem B o (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hmem, wv_writeW_top _ _ _ _ _ (by omega)]
    rw [h0, h1] at ho
    have st := Divstep.shr_step (P := 2 ^ (64 * j)) hI.val ho
    rw [wv, pow64_succ, show eS + 8 * (j + 1) = eS + 8 * j + 8 by omega]
    exact st

/-- `shrP s o`: `[o] := [s] >> 59`, arithmetic, `n + 1` words: as signed
numbers `2^59 [o] + ([s] mod 2^59) = [s]`. `[o]` may be `[s]`. -/
theorem shrP_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hn1 : 1 ≤ n) (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iS iO : Nat} (hS : iS < 16) (hO : iO < 16) :
    WP isa (shrP iS iO) s fun t =>
      2 ^ 59 * Divstep.sgn (n + 1) (wv t.mem B (slot w iO) (n + 1)) + (wv s.mem B (slot w iS) (n + 1) % 2 ^ 59 : Nat) =
        Divstep.sgn (n + 1) (wv s.mem B (slot w iS) (n + 1)) ∧
      Outside B (slot w iO) (8 * (n + 1)) s.mem t.mem ∧ Keep [.x3, .x4, .x13, .x14, .x16, .x17] s t ∧ t.v = s.v := by
  have hn' := hs.nowrap
  have sS := Nat.le_trans (slot_lt (w := w) hS) hZ
  have sO := Nat.le_trans (slot_lt (w := w) hO) hZ
  have sep : slot w iO ≤ slot w iS ∨ slot w iS + 8 * (n + 1) ≤ slot w iO := by
    by_cases h : iO = iS
    · subst h; exact .inl (Nat.le_refl _)
    · rcases slot_sep (w := w) h with h' | h' <;> [exact .inl (by omega); exact .inr (by omega)]
  have hvn : (shrP iS iO).allInstrs (fun i => (vdstOf i).isNone) = true := by
    simp only [shrP, Code.allInstrs_eq, instrs, List.all_append, base_vnone]; decide
  suffices h : WP isa (shrP iS iO) s fun t =>
      2 ^ 59 * Divstep.sgn (n + 1) (wv t.mem B (slot w iO) (n + 1)) + (wv s.mem B (slot w iS) (n + 1) % 2 ^ 59 : Nat) =
        Divstep.sgn (n + 1) (wv s.mem B (slot w iS) (n + 1)) ∧
      Outside B (slot w iO) (8 * (n + 1)) s.mem t.mem ∧ Keep [.x3, .x4, .x13, .x14, .x16, .x17] s t from
    WP.mono (WP.vfix h hvn) fun t ⟨⟨a, b, c⟩, v⟩ => ⟨a, b, c, v⟩
  unfold shrP
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (base2_ok iS iO .x16 .x17 h0 h11)
    fun s₁ ⟨⟨h16, h17, m₁, _⟩, k₁⟩ => WP.mono (WP.keep [.x14] (Q := fun t =>
      t.gpr .x14 = BitVec.ofNat 64 n ∧ t.mem = s₁.mem)
      (by brun [(k₁.gpr .x12 (by decide)).trans h12]) (by decide) (by decide) (by decide +kernel))
    fun s₂ ⟨⟨h14, m₂⟩, k₂⟩ => ?_))
  have hm : s₂.mem = s.mem := m₂.trans m₁
  have I0 : Shr59Inv s₂ B Z (slot w iS) (slot w iO) 0 s₂ :=
    ⟨hs.congr (k₁.trans k₂).wr, Keep.refl _ _, by rw [k₂.gpr .x16 (by decide), h16]; rfl,
      by rw [k₂.gpr .x17 (by decide), h17]; rfl, Outside.refl _ _ _ _, by
        simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.mul_zero]
        omega⟩
  refine WP.seq (WP.mono (wp_countdown (N := n) (by omega) (by omega) (Shr59Inv s₂ B Z (slot w iS) (slot w iO))
    (fun j hj t hI _ => shr59Step_ok (by omega) (by omega) sep hj hI) I0 h14) fun u hI => ?_)
  refine WP.mono (WP.keep [.x3, .x4, .x13] (shrTop_ok u hI.scr hI.x16 hI.x17 (by omega) (by omega))
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨o, hmt, ho⟩, kt⟩ => ⟨?_, ?_, ?_⟩
  · have hsn : word u.mem B (slot w iS + 8 * n) = word s₂.mem B (slot w iS + 8 * n) :=
      hI.out.word (by omega) (by omega)
    rw [hsn] at ho
    have st := Divstep.shr_step (P := 2 ^ (64 * n)) hI.val ho
    have hW := wv_lt s₂.mem B (slot w iS) n
    have hsl := (word s₂.mem B (slot w iS + 8 * n)).isLt
    have fin := Divstep.shr_final (L := n + 1) (S := wv s₂.mem B (slot w iS) (n + 1))
      (O := wv t.mem B (slot w iO) (n + 1)) (by omega) (wv_lt _ _ _ _) (wv_lt _ _ _ _) (Nat.mod_lt _ (by decide))
      (M := if (word s₂.mem B (slot w iS + 8 * n)).toNat < 2 ^ 63 then 0 else 2 ^ 64 - 1)
      (by rw [wv]; simp only [Divstep.top_sign hW hsl]) (by
        rw [hmt, wv_writeW_top _ _ _ _ _ (by omega), pow64_succ]
        rw [wv] at st ⊢
        exact st)
    rw [← hm, ← fin, ← wv_mod64 _ _ _ (show 1 ≤ n + 1 by omega), Nat.mod_mod_of_dvd _ (by decide)]
  · rw [← hm, hmt]
    refine fun x hx' => ?_
    rw [writeW_outside u.mem B o (by omega) x (by omega)]
    exact hI.out x (by omega)
  · exact (((k₁.trans k₂).trans hI.keep).trans kt).mono (by decide)
end VG.Proof.Rsa.AArch64

-- From `Proof/Rsa/AArch64/InvMred.lean`.
/-!
# RSA private keys on AArch64: the batched inverse's Montgomery word

`mredP a m o`: `[o] := mredRaw ([a])` for the signed `[a]` of `n + 1`
words (`mredP_ok`): `[a]` sign-extended by a word (`mredMid_ok`, which also
takes the digit `k = a₀ (-m⁻¹)`), `k m` added modulo `2^(64 (n + 2))`
(`mulAddRowMod_ok`: `mulAddRow` when the sum may wrap), and its words above
the lowest copied down (`copyLoop_ok`; `[o]` may be `[a]`).
-/


namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- Two words plus a carry and its carry, modulo `2^128`. -/
theorem addc2_mod (X Y c : BitVec 64) :
    (X + c).toNat + 2 ^ 64 * (Y + BitVec.ofNat 64 (decide (2 ^ 64 ≤ X.toNat + c.toNat)).toNat).toNat =
      (X.toNat + c.toNat + 2 ^ 64 * Y.toNat) % 2 ^ 128 := by
  have hX := X.isLt; have hY := Y.isLt; have hc := c.isLt
  by_cases h : 2 ^ 64 ≤ X.toNat + c.toNat <;>
  simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false, BitVec.toNat_add,
    BitVec.toNat_ofNat] <;> omega

/-- `(a + P b) mod P Q`, for `a < P`. -/
theorem add_mul_mod_mul {a b P Q : Nat} (ha : a < P) : (a + P * b) % (P * Q) = a + P * (b % Q) := by
  rw [Nat.mod_mul, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.add_mul_div_left _ _ (by omega),
    Nat.div_eq_of_lt ha, Nat.zero_add]

/-- The value after `rowTop`, modulo `2^(64 (w + 2))`. -/
theorem rowTop_valMod (m : Mem) (B : Addr) {Z eA w : Nat} (hn : B.toNat + Z ≤ 2 ^ 64)
    (hA : eA + 8 * w + 16 ≤ Z) (c : BitVec 64) :
    wv ((m.writeW (off B (eA + 8 * w)) (word m B (eA + 8 * w) + c)).writeW
        (off B (eA + 8 * w + 8)) (word m B (eA + 8 * w + 8) + BitVec.ofNat 64
          (decide (2 ^ 64 ≤ (word m B (eA + 8 * w)).toNat + c.toNat)).toNat))
        B eA (w + 2) =
      (wv m B eA w + 2 ^ (64 * w) * ((word m B (eA + 8 * w)).toNat + c.toNat +
        2 ^ 64 * (word m B (eA + 8 * w + 8)).toNat)) % 2 ^ (64 * (w + 2)) := by
  have o1 := writeW_outside m B (word m B (eA + 8 * w) + c) (d := eA + 8 * w) (by omega)
  have o2 := writeW_outside (m.writeW (off B (eA + 8 * w)) (word m B (eA + 8 * w) + c)) B
    (word m B (eA + 8 * w + 8) + BitVec.ofNat 64
      (decide (2 ^ 64 ≤ (word m B (eA + 8 * w)).toNat + c.toNat)).toNat)
    (d := eA + 8 * w + 8) (by omega)
  have hc := addc2_mod (word m B (eA + 8 * w)) (word m B (eA + 8 * w + 8)) c
  rw [show w + 2 = w + 1 + 1 from rfl, wv, wv, show eA + 8 * (w + 1) = eA + 8 * w + 8 by omega,
    word_writeW_self, o2.word (Or.inl (Nat.le_refl _)) (by omega), word_writeW_self,
    o2.wv (Or.inl (by omega)) (by omega), o1.wv (Or.inl (Nat.le_refl _)) (by omega), pow64_succ,
    show 2 ^ (64 * (w + 1 + 1)) = 2 ^ (64 * w) * 2 ^ 128 by rw [← Nat.pow_add]; congr 1,
    add_mul_mod_mul (wv_lt m B eA w), ← hc]
  grind

/-- `acc += x1 · B` modulo `2^(64 (w + 2))` (`mulAddRow`). -/
theorem mulAddRowMod_ok {s : State} {B : Addr} {Z w eA eb : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .x8 = off B eA) (h9 : s.gpr .x9 = off B eb) (h12 : s.gpr .x12 = BitVec.ofNat 64 w)
    (h7 : s.gpr .x7 = 0) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : eA + 8 * (w + 2) ≤ Z) (hb : eb + 8 * w ≤ Z)
    (hsep : eA + 8 * (w + 2) ≤ eb ∨ eb + 8 * w ≤ eA) :
    WP isa mulAddRow s fun t =>
      wv t.mem B eA (w + 2) = (wv s.mem B eA (w + 2) + (s.gpr .x1).toNat * wv s.mem B eb w) % 2 ^ (64 * (w + 2)) ∧
      Outside B eA (8 * (w + 2)) s.mem t.mem ∧ Keep [.x2, .x3, .x4, .x14, .x16, .x17] s t := by
  have hn := hs.nowrap
  unfold mulAddRow
  refine WP.seq (WP.mono (WP.keep [.x2, .x14, .x16, .x17] (Q := fun t => t.gpr .x16 = off B eA ∧
    t.gpr .x17 = off B eb ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧ t.gpr .x2 = 0 ∧ t.c = false ∧ t.mem = s.mem)
    (by brun [h8, h9, h12, h7]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h16, h17, h14, h2, hcf, hm₁⟩, k₁⟩ => ?_)
  have s₁7 : s₁.gpr .x7 = 0 := (k₁.gpr .x7 (by decide)).trans h7
  have s₁1 : s₁.gpr .x1 = s.gpr .x1 := k₁.gpr .x1 (by decide)
  have h0 : RowInv s₁ B Z eA eb 0 s₁ :=
    ⟨hs.congr k₁.wr, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, Outside.refl _ _ _ _,
      by simp only [carry, h2, hcf, Bool.toNat_false]; rfl,
      by simp only [carry, h2, hcf, Bool.toNat_false]; decide⟩
  refine WP.seq (WP.mono (wp_countdown (N := w) (by omega) (by omega) (RowInv s₁ B Z eA eb)
    (fun j hj t hI _ => rowStep_ok s₁7 (by omega) hb (by omega) hj hI) h0 h14) fun u hI => ?_)
  have u7 : u.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans s₁7
  refine WP.seq (WP.mono (carryOut_ok u u7 hI.carry_lt) fun t ⟨⟨hm, hcarry⟩, kc⟩ => ?_)
  have t7 : t.gpr .x7 = 0 := (kc.gpr .x7 (by decide)).trans u7
  refine WP.mono (rowTop_ok (hI.scr.congr kc.wr)
    ((kc.gpr .x16 (by decide)).trans hI.x16) t7 (by omega)) fun t' ⟨hm', k'⟩ => ?_
  have hX : word t.mem B (eA + 8 * w) = word s.mem B (eA + 8 * w) := by
    rw [hm, hI.out.word (Or.inr (Nat.le_refl _)) (by omega), hm₁]
  have hY : word t.mem B (eA + 8 * w + 8) = word s.mem B (eA + 8 * w + 8) := by
    rw [hm, hI.out.word (Or.inr (by omega)) (by omega), hm₁]
  have hval := hI.val
  rw [hm₁, s₁1, ← hcarry, ← hm] at hval
  have e2 := wv_top2 s.mem B eA w
  refine ⟨?_, ?_, (((k₁.trans hI.keep).trans kc).trans k').mono (by decide)⟩
  · have hc := hI.carry_lt
    rw [hm', rowTop_valMod t.mem B hn (show eA + 8 * w + 16 ≤ Z by omega) _, hX, hY, e2]
    congr 1
    grind
  · rw [hm']
    intro x hx
    rw [writeW_outside _ B _ (by omega) x (by omega), writeW_outside _ B _ (by omega) x (by omega)]
    rw [hm]
    exact (hI.out x (by omega)).trans (by rw [hm₁])
end VG.Proof.Bignum.AArch64

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.InvBatch
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The middle of `mredP`'s head: the digit `k = a₀ x5` into `x1`, and word
`n + 1` of `[x8]` the sign mask of its word `n`. -/
theorem mredMid_ok (s : State) {B : Addr} {Z eA n : Nat} (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eA)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 n) (hn : n < 2 ^ 24) (hA : eA + 8 * (n + 2) ≤ Z) :
    WP isa (.block ([ld .x3 .x8, .mul .x .x1 .x3 .x5, .lsl .x .x6 .x12 3, .add .x .x6 .x8 .x6, ld .x3 .x6,
      .lsr .x .x3 .x3 63, movi .x7 0, .sub .x .x3 .x7 .x3, st .x3 .x6 8] : List Instr)) s fun t =>
      (t.gpr .x1 = word s.mem B eA * s.gpr .x5 ∧ t.gpr .x7 = 0 ∧
        t.mem = s.mem.writeW (off B (eA + 8 * n + 8)) (0#64 - (word s.mem B (eA + 8 * n) >>> 63))) ∧
      Keep [.x1, .x3, .x6, .x7] s t := by
  have hn' := hs.nowrap
  refine WP.keep [.x1, .x3, .x6, .x7] ?_ (by decide) (by decide) (by decide +kernel)
  brun [h8, h12, shl_ofNat (show n * 2 ^ 3 < 2 ^ 64 by omega), hs.ld (show eA + 8 ≤ Z by omega),
    show off B eA + BitVec.ofNat 64 (n * 2 ^ 3) = off B (eA + 8 * n) by rw [off_add]; congr 2; omega,
    hs.ld (show eA + 8 * n + 8 ≤ Z by omega), hs.st (show eA + 8 * n + 8 + 8 ≤ Z by omega),
    show BitVec.setWidth 64 0#16 = 0#64 from rfl]

/-- After `j` words of `copyBody`. -/
structure MredCopyInv (s₀ : State) (B : Addr) (Z eS eO : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eS + 8 * j)
  x17 : t.gpr .x17 = off B (eO + 8 * j)
  out : Outside B eO (8 * j) s₀.mem t.mem
  val : wv t.mem B eO j = wv s₀.mem B eS j

/-- `L` words of `[x16]` to `[x17]`, ascending: `[x16]` may be `[x17]` plus
some words. -/
theorem copyLoop_ok {s : State} {B : Addr} {Z L eS eO : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eS) (h17 : s.gpr .x17 = off B eO) (h14 : s.gpr .x14 = BitVec.ofNat 64 L)
    (hL : 1 ≤ L) (hL' : L < 2 ^ 32) (hS : eS + 8 * L ≤ Z) (hO : eO + 8 * L ≤ Z)
    (sep : eO ≤ eS ∨ eS + 8 * L ≤ eO) :
    WP isa (countLoop .x14 copyBody) s (MredCopyInv s B Z eS eO L) := by
  have hn := hs.nowrap
  have h0 : MredCopyInv s B Z eS eO 0 s :=
    ⟨hs, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, Outside.refl _ _ _ _, rfl⟩
  refine wp_countdown (N := L) (by omega) (by omega) (MredCopyInv s B Z eS eO) (fun j hj t hI _ => ?_) h0 h14
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x16, .x17] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (eO + 8 * j)) (word t.mem B (eS + 8 * j)) ∧
      t₁.gpr .x16 = off B (eS + 8 * j + 8) ∧ t₁.gpr .x17 = off B (eO + 8 * j + 8))
    (by unfold copyBody; brun [hI.x16, hI.x17, hI.scr.ld (show eS + 8 * j + 8 ≤ Z by omega),
      hI.scr.st (show eO + 8 * j + 8 ≤ Z by omega)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, h16', h17'⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14', hm', _⟩, k'⟩ => ⟨?_, by rw [h14', k₁.gpr .x14 (by decide)]⟩
  have hmem : t'.mem = t.mem.writeW (off B (eO + 8 * j)) (word t.mem B (eS + 8 * j)) := hm'.trans hm
  have hx : word t.mem B (eS + 8 * j) = word s.mem B (eS + 8 * j) := hI.out.word (by omega) (by omega)
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16', Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17', Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hmem]
    refine fun x hx' => ?_
    rw [writeW_outside t.mem B _ (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hmem, wv_writeW_top _ _ _ _ _ (by omega), hI.val, hx]
    rfl
/-- `mredP a m o`: `[o] := mredRaw [a]` modulo `2^(64 (n + 1))`, `-m⁻¹` from lane 1 of `v18`. -/
theorem mredP_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hn1 : 1 ≤ n) (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iA iM iO : Nat}
    (hA : iA < 16) (hM : iM < 16) (hO : iO < 16) (dAM : iA ≠ iM) (dOM : iO ≠ iM) :
    WP isa (seqs (mredP iA iM iO)) s fun t =>
      (((wv s.mem B (slot w iM) n : Int) * ((s.v .v18).extractLsb' 64 64).toNat + 1) % 2 ^ 64 = 0 →
        (wv t.mem B (slot w iO) (n + 1) : Int) = Divstep.mredRaw (wv s.mem B (slot w iM) n)
        ((s.v .v18).extractLsb' 64 64).toNat (Divstep.sgn (n + 1) (wv s.mem B (slot w iA) (n + 1))) %
          2 ^ (64 * (n + 1))) ∧
      Frm B [(slot w iA, 8 * (n + 2)), (slot w iO, 8 * (n + 1))] s.mem t.mem ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x14, .x16, .x17] s t ∧ t.v = s.v := by
  have hn' := hs.nowrap
  have sA := Nat.le_trans (slot_lt (w := w) hA) hZ
  have sM := Nat.le_trans (slot_lt (w := w) hM) hZ
  have sO := Nat.le_trans (slot_lt (w := w) hO) hZ
  have pAM := slot_sep (w := w) dAM
  have pOM := slot_sep (w := w) dOM
  have sep : slot w iO ≤ slot w iA + 8 ∨ slot w iA + 8 + 8 * (n + 1) ≤ slot w iO := by
    by_cases h : iO = iA
    · subst h; exact .inl (by omega)
    · rcases slot_sep (w := w) h with h' | h' <;> [exact .inl (by omega); exact .inr (by omega)]
  have hvn : (seqs (mredP iA iM iO)).allInstrs (fun i => (vdstOf i).isNone) = true := by
    simp only [mredP, seqs, mulAddRow, Code.allInstrs_eq, instrs, List.all_append, base_vnone]; decide
  suffices h : WP isa (seqs (mredP iA iM iO)) s fun t =>
      (((wv s.mem B (slot w iM) n : Int) * ((s.v .v18).extractLsb' 64 64).toNat + 1) % 2 ^ 64 = 0 →
        (wv t.mem B (slot w iO) (n + 1) : Int) = Divstep.mredRaw (wv s.mem B (slot w iM) n)
        ((s.v .v18).extractLsb' 64 64).toNat (Divstep.sgn (n + 1) (wv s.mem B (slot w iA) (n + 1))) %
          2 ^ (64 * (n + 1))) ∧
      Frm B [(slot w iA, 8 * (n + 2)), (slot w iO, 8 * (n + 1))] s.mem t.mem ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x14, .x16, .x17] s t from
    WP.mono (WP.vfix h hvn) fun t ⟨⟨a, b, c⟩, v⟩ => ⟨a, b, c, v⟩
  simp only [mredP, seqs, List.append_assoc]
  -- The head: `x5 := -m⁻¹`, `x8 := A`, the digit and the sign extension, `x9 := M`.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.x5] (Q := fun t =>
      t.gpr .x5 = (s.v .v18).extractLsb' 64 64 ∧ t.mem = s.mem)
      (by brun [exec_umov_x, Nat.mul_one]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h5, m₁⟩, k₁⟩ => WP.block_append_iff.mpr (WP.mono (base_ok iA .x8 ((k₁.gpr .x0 (by decide)).trans h0)
      ((k₁.gpr .x11 (by decide)).trans h11))
    fun s₂ ⟨⟨h8, m₂, _⟩, k₂⟩ => WP.block_append_iff.mpr (WP.mono (mredMid_ok s₂ (hs.congr (k₁.trans k₂).wr) h8
      (((k₁.trans k₂).gpr .x12 (by decide)).trans h12) (by omega) (by omega))
    fun s₃ ⟨⟨h1, h7, m₃⟩, k₃⟩ => WP.mono (base_ok iM .x9 (((k₁.trans k₂).trans k₃ |>.gpr .x0 (by decide)).trans h0)
      (((k₁.trans k₂).trans k₃ |>.gpr .x11 (by decide)).trans h11))
    fun s₄ ⟨⟨h9, m₄, _⟩, k₄⟩ => ?_))))
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have e8 : s₄.gpr .x8 = off B (slot w iA) := (k₄.gpr .x8 (by decide)).trans ((k₃.gpr .x8 (by decide)).trans h8)
  have e7 : s₄.gpr .x7 = 0 := (k₄.gpr .x7 (by decide)).trans h7
  have e1 : s₄.gpr .x1 = word s₂.mem B (slot w iA) * s₂.gpr .x5 := (k₄.gpr .x1 (by decide)).trans h1
  have e12 : s₄.gpr .x12 = BitVec.ofNat 64 n := (k14.gpr .x12 (by decide)).trans h12
  have hm₄ : s₄.mem = s.mem.writeW (off B (slot w iA + 8 * n + 8))
      (0#64 - (word s.mem B (slot w iA + 8 * n) >>> 63)) := by rw [m₄, m₃, m₂, m₁]
  -- `[a] += k m`.
  refine WP.seq (WP.mono (mulAddRowMod_ok (hs.congr k14.wr) e8 h9 e12 e7 hn1 (by omega) (by omega) (by omega)
    (by omega)) fun s₅ ⟨hv₅, o₅, k₅⟩ => ?_)
  have k15 := k14.trans k₅
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (base_ok iA .x16 ((k15.gpr .x0 (by decide)).trans h0)
      ((k15.gpr .x11 (by decide)).trans h11))
    fun s₆ ⟨⟨h16, m₆, _⟩, k₆⟩ => WP.block_append_iff.mpr (WP.mono (WP.keep [.x16] (Q := fun t =>
      t.gpr .x16 = off B (slot w iA + 8) ∧ t.mem = s₆.mem) (by brun [h16]) (by decide) (by decide)
      (by decide +kernel))
    fun s₇ ⟨⟨h16', m₇⟩, k₇⟩ => WP.block_append_iff.mpr (WP.mono (base_ok iO .x17
      (((k15.trans k₆).trans k₇ |>.gpr .x0 (by decide)).trans h0)
      (((k15.trans k₆).trans k₇ |>.gpr .x11 (by decide)).trans h11))
    fun s₈ ⟨⟨h17, m₈, _⟩, k₈⟩ => WP.mono (WP.keep [.x14] (Q := fun t =>
      t.gpr .x14 = BitVec.ofNat 64 (n + 1) ∧ t.mem = s₈.mem)
      (by brun [((((k15.trans k₆).trans k₇).trans k₈).gpr .x12 (by decide)).trans h12, cntL]
          exact BitVec.ofNat_add_ofNat (n := 64) n 1) (by decide) (by decide) (by decide +kernel))
    fun s₉ ⟨⟨h14, m₉⟩, k₉⟩ => ?_))))
  have hm₉ : s₉.mem = s₅.mem := by rw [m₉, m₈, m₇, m₆]
  refine WP.mono (copyLoop_ok (hs.congr ((((k15.trans k₆).trans k₇).trans k₈).trans k₉).wr)
    ((k₉.gpr .x16 (by decide)).trans ((k₈.gpr .x16 (by decide)).trans h16')) ((k₉.gpr .x17 (by decide)).trans h17)
    h14 (by omega) (by omega) (by omega) (by omega) sep) fun t hI => ⟨fun hm => ?_, ?_, ?_⟩
  · have hO := hI.val
    rw [hm₉] at hO
    -- The sign extension.
    have hS := wv_lt s.mem B (slot w iA) n
    have hsl := (word s.mem B (slot w iA + 8 * n)).isLt
    have hW₁ : wv s₄.mem B (slot w iA) (n + 2) = wv s.mem B (slot w iA) (n + 1) + 2 ^ (64 * (n + 1)) *
        (if wv s.mem B (slot w iA) (n + 1) < 2 ^ (64 * (n + 1) - 1) then 0 else 2 ^ 64 - 1) := by
      rw [hm₄, show slot w iA + 8 * n + 8 = slot w iA + 8 * (n + 1) by omega,
        wv_writeW_top _ _ _ _ _ (by omega), Divstep.signMask_eq]
      rw [wv]; simp only [Divstep.top_sign hS hsl]
      split <;> rfl
    have hM₄ : wv s₄.mem B (slot w iM) n = wv s.mem B (slot w iM) n := by
      rw [hm₄]; exact (writeW_outside _ B _ (by omega)).wv (by omega) (by omega)
    have hk : (s₄.gpr .x1).toNat = (wv s.mem B (slot w iA) (n + 1) % 2 ^ 64) *
        ((s.v .v18).extractLsb' 64 64).toNat % 2 ^ 64 := by
      have e5 : s₂.gpr .x5 = (s.v .v18).extractLsb' 64 64 := (k₂.gpr .x5 (by decide)).trans h5
      rw [e1, BitVec.toNat_mul, e5, m₂, m₁, wv_mod64 _ _ _ (by omega)]
    rw [hW₁, hM₄, show n + 2 = n + 1 + 1 from rfl] at hv₅
    have hsplit := wv_add s₅.mem B (slot w iA) 1 (n + 1)
    rw [show 1 + (n + 1) = n + 2 by omega] at hsplit
    refine Divstep.mredSext_words (L := n + 1) (W₂ := wv s₅.mem B (slot w iA) (n + 2)) (by omega) hm
      (k := ((s₄.gpr .x1).toNat : Int)) ?_ ?_ ?_
    · exact_mod_cast hk
    · exact_mod_cast hv₅
    · rw [hsplit, ← hO, Nat.mul_one]
      have := wv_lt s₅.mem B (slot w iA) 1
      rw [Nat.mul_one] at this
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt this]
  · have f1 : Frm B [(slot w iA, 8 * (n + 2)), (slot w iO, 8 * (n + 1))] s.mem s₄.mem := by
      rw [hm₄]
      exact Frm.of_outside (Outside.mono (o' := slot w iA) (n' := 8 * (n + 2)) (writeW_outside _ B _ (by omega))
        (by omega) (by omega)) (by simp)
    have f3 : Frm B [(slot w iA, 8 * (n + 2)), (slot w iO, 8 * (n + 1))] s₅.mem t.mem := by
      rw [← hm₉]; exact Frm.of_outside hI.out (by simp)
    exact (f1.trans (Frm.of_outside o₅ (by simp))).trans f3
  · exact ((((((k15.trans k₆).trans k₇).trans k₈).trans k₉).trans hI.keep)).mono (by decide)
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
  rw [shl_ofNat (show S * 2 ^ 32 < 2 ^ 64 by omega), BitVec.ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

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
      t.mem = s₁.mem ∧ t.v = s₁.v) (by brun [h2, m₁, (hs.congr k₁.wr).ld (show slot w iF + 8 ≤ Z by omega), RegUpd.v_write]) (by decide) (by decide)
      (by decide +kernel)) fun s₂ ⟨⟨h2', m₂, v₂⟩, k₂⟩ =>
    WP.block_append_iff.mpr (WP.mono (WP.vfix (base_ok iG .x3 ((k₁.trans k₂ |>.gpr .x0 (by decide)).trans h0)
      ((k₁.trans k₂ |>.gpr .x11 (by decide)).trans h11)) (bv _ _)) fun s₃ ⟨⟨⟨h3, m₃, _⟩, k₃⟩, v₃⟩ => ?_)))
  have k13 := (k₁.trans k₂).trans k₃
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x1, .x3] (Q := fun t => t.gpr .x3 = word s.mem B (slot w iG) ∧
      t.gpr .x1 = laneOf s .v18 0 ∧ t.mem = s₃.mem ∧ t.v = s₃.v)
      (by brun [h3, m₃, m₂, m₁, (hs.congr k13.wr).ld (show slot w iG + 8 ≤ Z by omega), RegUpd.v_write, exec_umov,
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
  refine WP.mono (headTail_ok' s₆ (S := 8 * (w + 2)) (N := n) (by omega) (by omega)
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
  exact h.wv (by rcases slot_apart (w := w) (a := 8 * L) (b := n) hjo.symm (by omega) hn with h' | h' <;> omega) (by omega)

/-- The `f`, `g` half of a batch: `(f, g) := (u f + v g, q f + r g) / 2^59`. -/
theorem fgStage_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hn1 : 1 ≤ n) (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iF iG iT : Nat}
    (hF : iF < 16) (hG : iG < 16) (hT : iT < 16) (dFG : iF ≠ iG) (dFT : iF ≠ iT) (dGT : iG ≠ iT)
    {u v q r f g f' g' : Int} (huv : |u| + |v| ≤ 2 ^ 59) (hqr : |q| + |r| ≤ 2 ^ 59)
    (lu : laneOf s .v16 0 = BitVec.ofInt 64 u) (lv : laneOf s .v16 1 = BitVec.ofInt 64 v)
    (lq : laneOf s .v17 0 = BitVec.ofInt 64 q) (lr : laneOf s .v17 1 = BitVec.ofInt 64 r)
    (hf : sgn (n + 1) (wv s.mem B (slot w iF) (n + 1)) = f) (hg : sgn (n + 1) (wv s.mem B (slot w iG) (n + 1)) = g)
    (bf : |f| < 2 ^ (64 * n + 1)) (bg : |g| < 2 ^ (64 * n + 1))
    (ef : u * f + v * g = 2 ^ 59 * f') (eg : q * f + r * g = 2 ^ 59 * g') :
    WP isa (seqs [rowP .v16 iF iG iT, rowP .v17 iF iG iG, shrP iT iF, shrP iG iG]) s fun t =>
      sgn (n + 1) (wv t.mem B (slot w iF) (n + 1)) = f' ∧ sgn (n + 1) (wv t.mem B (slot w iG) (n + 1)) = g' ∧
      Frm B [(slot w iT, 8 * (n + 1)), (slot w iG, 8 * (n + 1)), (slot w iF, 8 * (n + 1))] s.mem t.mem ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x13, .x14, .x16, .x17] s t ∧ t.v = s.v := by
  have hn' := hs.nowrap
  have hZ' : slot w 16 + B.toNat ≤ 2 ^ 64 := by omega
  obtain ⟨u0, u1, v0, v1, uvA⟩ := Rsa.Divstep.row_parts huv
  obtain ⟨q0, q1, r0, r1, qrA⟩ := Rsa.Divstep.row_parts hqr
  obtain ⟨f0, f1⟩ := Rsa.Divstep.abs_lt_parts bf
  obtain ⟨g0, g1⟩ := Rsa.Divstep.abs_lt_parts bg
  have tu : (laneOf s .v16 0).toInt = u := by rw [lu]; exact Divstep.toInt_ofInt64 (by omega) (by omega)
  have tv : (laneOf s .v16 1).toInt = v := by rw [lv]; exact Divstep.toInt_ofInt64 (by omega) (by omega)
  have tq : (laneOf s .v17 0).toInt = q := by rw [lq]; exact Divstep.toInt_ofInt64 (by omega) (by omega)
  have tr : (laneOf s .v17 1).toInt = r := by rw [lr]; exact Divstep.toInt_ofInt64 (by omega) (by omega)
  have hL : (1 : Nat) ≤ n + 1 := by omega
  obtain ⟨cr10, cr11⟩ := Rsa.Divstep.comb_range huv bf bg
  obtain ⟨cr20, cr21⟩ := Rsa.Divstep.comb_range hqr bf bg
  simp only [seqs]
  -- `[t] := u f + v g`.
  refine WP.seq (WP.mono (rowP_ok hs h0 h11 h12 hn hw hZ (.inl rfl) hF hG hT
    (by simp only [laneOf, Nat.mul_zero, Nat.mul_one] at tu tv; rw [tu, tv]; exact uvA))
    fun s₁ ⟨c₁, e₁, o₁, k₁, v₁⟩ => ?_)
  have F₁ := wv_out (L := n + 1) o₁ dFT.symm (by omega) (by omega) hZ' hF
  have G₁ := wv_out (L := n + 1) o₁ dGT.symm (by omega) (by omega) hZ' hG
  have sT : sgn (n + 1) (wv s₁.mem B (slot w iT) (n + 1)) = u * f + v * g := by
    simp only [laneOf, Nat.mul_zero, Nat.mul_one] at tu tv
    rw [tu, tv] at e₁
    rw [← hf, ← hg]
    exact Divstep.lin_sgn hL (wv_lt _ _ _ _) (wv_lt _ _ _ _) (wv_lt _ _ _ _) e₁ (by rw [hf, hg]; exact cr10)
      (by rw [hf, hg]; exact cr11)
  -- `[g] := q f + r g`.
  have e0 : s₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h0
  have e11 : s₁.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) := (k₁.gpr .x11 (by decide)).trans h11
  have e12 : s₁.gpr .x12 = BitVec.ofNat 64 n := (k₁.gpr .x12 (by decide)).trans h12
  have tq' : (laneOf s₁ .v17 0).toInt = q := by rw [laneOf, v₁]; exact tq
  have tr' : (laneOf s₁ .v17 1).toInt = r := by rw [laneOf, v₁]; exact tr
  simp only [laneOf, Nat.mul_zero, Nat.mul_one] at tq' tr'
  refine WP.seq (WP.mono (rowP_ok (hs.congr k₁.wr) e0 e11 e12 hn hw hZ (.inr rfl) hF hG hG
    (by rw [tq', tr']; exact qrA)) fun s₂ ⟨c₂, e₂, o₂, k₂, v₂⟩ => ?_)
  have sG₂ : sgn (n + 1) (wv s₂.mem B (slot w iG) (n + 1)) = q * f + r * g := by
    rw [tq', tr', F₁, G₁] at e₂
    rw [← hf, ← hg]
    exact Divstep.lin_sgn hL (wv_lt _ _ _ _) (wv_lt _ _ _ _) (wv_lt _ _ _ _) e₂ (by rw [hf, hg]; exact cr20)
      (by rw [hf, hg]; exact cr21)
  have T₂ := wv_out (L := n + 1) o₂ dGT (by omega) (by omega) hZ' hT
  have F₂ := wv_out (L := n + 1) o₂ dFG.symm (by omega) (by omega) hZ' hF
  -- `[f] := [t] >> 59`.
  have k12 := k₁.trans k₂
  refine WP.seq (WP.mono (shrP_ok (hs.congr k12.wr) ((k12.gpr .x0 (by decide)).trans h0)
    ((k12.gpr .x11 (by decide)).trans h11) ((k12.gpr .x12 (by decide)).trans h12) hn1 hn hw hZ hT hF)
    fun s₃ ⟨e₃, o₃, k₃, v₃⟩ => ?_)
  have hf' : sgn (n + 1) (wv s₃.mem B (slot w iF) (n + 1)) = f' := by
    rw [T₂, sT, ef] at e₃
    have := Nat.mod_lt (wv s₁.mem B (slot w iT) (n + 1)) (show 0 < 2 ^ 59 by decide)
    omega
  have G₃ := wv_out (L := n + 1) o₃ dFG (by omega) (by omega) hZ' hG
  -- `[g] := [g] >> 59`.
  have k13 := k12.trans k₃
  refine WP.mono (shrP_ok (hs.congr k13.wr) ((k13.gpr .x0 (by decide)).trans h0)
    ((k13.gpr .x11 (by decide)).trans h11) ((k13.gpr .x12 (by decide)).trans h12) hn1 hn hw hZ hG hG)
    fun t ⟨e₄, o₄, k₄, v₄⟩ => ⟨?_, ?_, ?_, (k13.trans k₄).mono (by decide), by rw [v₄, v₃, v₂, v₁]⟩
  · rw [wv_out (L := n + 1) o₄ dFG.symm (by omega) (by omega) hZ' hF]; exact hf'
  · rw [G₃, sG₂, eg] at e₄
    have := Nat.mod_lt (wv s₂.mem B (slot w iG) (n + 1)) (show 0 < 2 ^ 59 by decide)
    omega
  · exact (((Frm.of_outside o₁ (by simp)).trans (Frm.of_outside o₂ (by simp))).trans
      (Frm.of_outside o₃ (by simp))).trans (Frm.of_outside o₄ (by simp))

/-- A frame by smaller ranges is one by larger. -/
theorem Frm.widen {B : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m')
    (hs : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Frm B rs' m m' :=
  fun x hx => h x fun r hr => by
    obtain ⟨r', hr', h1, h2⟩ := hs r hr
    have := hx r' hr'
    omega

/-- The `a`, `b` half of a batch: `(a, b) := (mredRaw (u a + v b), mredRaw (q a + r b))`
where `-m⁻¹` is right and `a`, `b` and the results are in `(-p, 2p)`. -/
theorem abStage_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hn1 : 1 ≤ n) (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iA iB iT iM : Nat}
    (hA : iA < 16) (hB : iB < 16) (hT : iT < 16) (hM : iM < 16) (dAB : iA ≠ iB) (dAT : iA ≠ iT) (dBT : iB ≠ iT)
    (dAM : iA ≠ iM) (dBM : iB ≠ iM) (dTM : iT ≠ iM)
    {u v q r a b a' b' : Int} {p : Nat} (hp : p < 2 ^ (64 * n)) (huv : |u| + |v| ≤ 2 ^ 59) (hqr : |q| + |r| ≤ 2 ^ 59)
    (lu : laneOf s .v16 0 = BitVec.ofInt 64 u) (lv : laneOf s .v16 1 = BitVec.ofInt 64 v)
    (lq : laneOf s .v17 0 = BitVec.ofInt 64 q) (lr : laneOf s .v17 1 = BitVec.ofInt 64 r)
    (ea : a' = Divstep.mredRaw p (laneOf s .v18 1).toNat (u * a + v * b))
    (eb : b' = Divstep.mredRaw p (laneOf s .v18 1).toNat (q * a + r * b)) :
    WP isa (seqs ([rowP .v16 iA iB iT, rowP .v17 iA iB iB] ++ mredP iT iM iA ++ mredP iB iM iB)) s fun t =>
      ((((p : Int) * (laneOf s .v18 1).toNat + 1) % 2 ^ 64 = 0 ∧ wv s.mem B (slot w iM) n = p ∧
        sgn (n + 1) (wv s.mem B (slot w iA) (n + 1)) = a ∧ sgn (n + 1) (wv s.mem B (slot w iB) (n + 1)) = b ∧
        (-(p : Int) < a ∧ a < 2 * p) ∧ (-(p : Int) < b ∧ b < 2 * p) ∧
        (-(p : Int) < a' ∧ a' < 2 * p) ∧ (-(p : Int) < b' ∧ b' < 2 * p)) →
        sgn (n + 1) (wv t.mem B (slot w iA) (n + 1)) = a' ∧ sgn (n + 1) (wv t.mem B (slot w iB) (n + 1)) = b') ∧
      Frm B [(slot w iT, 8 * (w + 2)), (slot w iA, 8 * (w + 2)), (slot w iB, 8 * (w + 2))] s.mem t.mem ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x13, .x14, .x16, .x17] s t ∧ t.v = s.v := by
  have hn' := hs.nowrap
  have hZ' : slot w 16 + B.toNat ≤ 2 ^ 64 := by omega
  obtain ⟨u0, u1, v0, v1, uvA⟩ := Rsa.Divstep.row_parts huv
  obtain ⟨q0, q1, r0, r1, qrA⟩ := Rsa.Divstep.row_parts hqr
  have tu : (laneOf s .v16 0).toInt = u := by rw [lu]; exact Divstep.toInt_ofInt64 (by omega) (by omega)
  have tv : (laneOf s .v16 1).toInt = v := by rw [lv]; exact Divstep.toInt_ofInt64 (by omega) (by omega)
  have tq : (laneOf s .v17 0).toInt = q := by rw [lq]; exact Divstep.toInt_ofInt64 (by omega) (by omega)
  have tr : (laneOf s .v17 1).toInt = r := by rw [lr]; exact Divstep.toInt_ofInt64 (by omega) (by omega)
  simp only [laneOf, Nat.mul_zero, Nat.mul_one] at tu tv tq tr
  have hL : (1 : Nat) ≤ n + 1 := by omega
  rw [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [mredP]) ?_
  simp only [seqs]
  -- `[t] := u a + v b`, `[b] := q a + r b`.
  refine WP.seq (WP.mono (rowP_ok hs h0 h11 h12 hn hw hZ (.inl rfl) hA hB hT (by rw [tu, tv]; exact uvA))
    fun s₁ ⟨c₁, e₁, o₁, k₁, v₁⟩ => ?_)
  have A₁ := wv_out (L := n + 1) o₁ dAT.symm (by omega) (by omega) hZ' hA
  have B₁ := wv_out (L := n + 1) o₁ dBT.symm (by omega) (by omega) hZ' hB
  have M₁ := wv_out (L := n) o₁ dTM (by omega) (by omega) hZ' hM
  rw [tu, tv] at e₁
  have sT : sgn (n + 1) (wv s.mem B (slot w iA) (n + 1)) = a → sgn (n + 1) (wv s.mem B (slot w iB) (n + 1)) = b →
      (-(p : Int) < a ∧ a < 2 * p) → (-(p : Int) < b ∧ b < 2 * p) →
      sgn (n + 1) (wv s₁.mem B (slot w iT) (n + 1)) = u * a + v * b := fun ha hb ra rb => by
    obtain ⟨baa, -, -⟩ := Rsa.Divstep.range_parts ra hp
    obtain ⟨bbb, -, -⟩ := Rsa.Divstep.range_parts rb hp
    obtain ⟨cr10, cr11⟩ := Rsa.Divstep.comb_range huv baa bbb
    rw [← ha, ← hb]
    exact Divstep.lin_sgn hL (wv_lt _ _ _ _) (wv_lt _ _ _ _) (wv_lt _ _ _ _) e₁ (by rw [ha, hb]; exact cr10)
      (by rw [ha, hb]; exact cr11)
  have e0 : s₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h0
  have e11 : s₁.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) := (k₁.gpr .x11 (by decide)).trans h11
  have e12 : s₁.gpr .x12 = BitVec.ofNat 64 n := (k₁.gpr .x12 (by decide)).trans h12
  have tq' : ((s₁.v .v17).extractLsb' 0 64).toInt = q := by rw [v₁]; exact tq
  have tr' : ((s₁.v .v17).extractLsb' 64 64).toInt = r := by rw [v₁]; exact tr
  refine WP.mono (rowP_ok (hs.congr k₁.wr) e0 e11 e12 hn hw hZ (.inr rfl) hA hB hB
    (by rw [tq', tr']; exact qrA)) fun s₂ ⟨c₂, e₂, o₂, k₂, v₂⟩ => ?_
  rw [tq', tr', A₁, B₁] at e₂
  have sB₂ : sgn (n + 1) (wv s.mem B (slot w iA) (n + 1)) = a → sgn (n + 1) (wv s.mem B (slot w iB) (n + 1)) = b →
      (-(p : Int) < a ∧ a < 2 * p) → (-(p : Int) < b ∧ b < 2 * p) →
      sgn (n + 1) (wv s₂.mem B (slot w iB) (n + 1)) = q * a + r * b := fun ha hb ra rb => by
    obtain ⟨baa, -, -⟩ := Rsa.Divstep.range_parts ra hp
    obtain ⟨bbb, -, -⟩ := Rsa.Divstep.range_parts rb hp
    obtain ⟨cr20, cr21⟩ := Rsa.Divstep.comb_range hqr baa bbb
    rw [← ha, ← hb]
    exact Divstep.lin_sgn hL (wv_lt _ _ _ _) (wv_lt _ _ _ _) (wv_lt _ _ _ _) e₂ (by rw [ha, hb]; exact cr20)
      (by rw [ha, hb]; exact cr21)
  have T₂ := wv_out (L := n + 1) o₂ dBT (by omega) (by omega) hZ' hT
  have M₂ := wv_out (L := n) o₂ dBM (by omega) (by omega) hZ' hM
  have k12 := k₁.trans k₂
  have lm : (s₂.v .v18).extractLsb' 64 64 = laneOf s .v18 1 := by rw [v₂, v₁]
  -- `[a] := mredRaw [t]`.
  refine wp_seqs_append (by simp [mredP]) (by simp [mredP]) (WP.mono (mredP_ok (hs.congr k12.wr)
    ((k12.gpr .x0 (by decide)).trans h0) ((k12.gpr .x11 (by decide)).trans h11)
    ((k12.gpr .x12 (by decide)).trans h12) hn1 hn hw hZ hT hM hA dTM dAM) fun s₃ ⟨e₃, f₃, k₃, v₃⟩ => ?_)
  rw [lm, M₂, M₁, T₂] at e₃
  have B₃ : wv s₃.mem B (slot w iB) (n + 1) = wv s₂.mem B (slot w iB) (n + 1) :=
    f₃.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rcases slot_apart (w := w) (a := 8 * (n + 1)) (b := 8 * (n + 2)) dBT (by omega) (by omega) with h | h
        · exact .inl h
        · exact .inr h
      · rcases slot_apart (w := w) (a := 8 * (n + 1)) (b := 8 * (n + 1)) dAB.symm (by omega) (by omega) with h | h
        · exact .inl h
        · exact .inr h) (by have := slot_lt (w := w) hB; omega)
  have M₃ : wv s₃.mem B (slot w iM) n = wv s₂.mem B (slot w iM) n :=
    f₃.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rcases slot_apart (w := w) (a := 8 * n) (b := 8 * (n + 2)) dTM.symm (by omega) (by omega) with h | h
        · exact .inl h
        · exact .inr h
      · rcases slot_apart (w := w) (a := 8 * n) (b := 8 * (n + 1)) dAM.symm (by omega) (by omega) with h | h
        · exact .inl h
        · exact .inr h) (by have := slot_lt (w := w) hM; omega)
  have k13 := k12.trans k₃
  have lm' : (s₃.v .v18).extractLsb' 64 64 = laneOf s .v18 1 := by rw [v₃, lm]
  -- `[b] := mredRaw [b]`.
  refine WP.mono (mredP_ok (hs.congr k13.wr) ((k13.gpr .x0 (by decide)).trans h0)
    ((k13.gpr .x11 (by decide)).trans h11) ((k13.gpr .x12 (by decide)).trans h12) hn1 hn hw hZ hB hM hB dBM dBM)
    fun t ⟨e₄, f₄, k₄, v₄⟩ => ⟨fun ⟨hm, hpm, ha, hb, ra, rb, ra', rb'⟩ => ⟨?_, ?_⟩, ?_, (k13.trans k₄).mono (by decide),
      by rw [v₄, v₃, v₂, v₁]⟩
  · obtain ⟨-, ra0, ra1⟩ := Rsa.Divstep.range_parts ra' hp
    rw [hpm, sT ha hb ra rb, ← ea] at e₃
    rw [f₄.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rcases slot_apart (w := w) (a := 8 * (n + 1)) (b := 8 * (n + 2)) dAB (by omega) (by omega) with h | h
        · exact .inl h
        · exact .inr h
      · rcases slot_apart (w := w) (a := 8 * (n + 1)) (b := 8 * (n + 1)) dAB (by omega) (by omega) with h | h
        · exact .inl h
        · exact .inr h) (by have := slot_lt (w := w) hA; omega)]
    exact Divstep.sgn_of_emod hL ra0 ra1 (e₃ hm)
  · obtain ⟨-, rb0, rb1⟩ := Rsa.Divstep.range_parts rb' hp
    rw [lm', M₃, M₂, M₁, hpm, B₃, sB₂ ha hb ra rb, ← eb] at e₄
    exact Divstep.sgn_of_emod hL rb0 rb1 (e₄ hm)
  · refine (((Frm.widen (Frm.of_outside o₁ (List.mem_singleton.mpr rfl)) ?_).trans
      (Frm.widen (Frm.of_outside o₂ (List.mem_singleton.mpr rfl)) ?_)).trans (Frm.widen f₃ ?_)).trans
      (Frm.widen f₄ ?_)
    all_goals
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp <;> omega
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
  · exact slot_apart (w := w) hja (by omega) ha
  · exact slot_apart (w := w) hjb (by omega) hb
  · exact slot_apart (w := w) hjc (by omega) hc

/-- Array `j` is apart from the batches' arrays. -/
theorem apart5 {w j a b c d e L : Nat} (hja : j ≠ a) (hjb : j ≠ b) (hjc : j ≠ c) (hjd : j ≠ d) (hje : j ≠ e)
    (hL : L ≤ w + 2) :
    ∀ r ∈ [(slot w a, 8 * (w + 2)), (slot w b, 8 * (w + 2)), (slot w c, 8 * (w + 2)), (slot w d, 8 * (w + 2)),
      (slot w e, 8 * (w + 2))], slot w j + 8 * L ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact slot_apart (w := w) hja (by omega) (Nat.le_refl _)
  · exact slot_apart (w := w) hjb (by omega) (Nat.le_refl _)
  · exact slot_apart (w := w) hjc (by omega) (Nat.le_refl _)
  · exact slot_apart (w := w) hjd (by omega) (Nat.le_refl _)
  · exact slot_apart (w := w) hje (by omega) (Nat.le_refl _)

/-- A batch keeps `LInv`, one batch on. -/
theorem batch_ok {C : ICfg} (hC : C.Ok) {s₀ s : State} {k : Nat} (hk : k < 3 * C.n + 2) (hI : LInv C s₀ k s) :
    WP isa (batch C.iV C.iU C.iX₂ C.iX₁ C.iT C.iM) s fun t =>
      LInv C s₀ (k + 1) t ∧ t.gpr .x15 = s.gpr .x15 - 1#64 := by
  have hn' := hI.scr.nowrap
  have hZ' : slot C.w 16 + C.B.toNat ≤ 2 ^ 64 := by have := hC.hZ; omega
  have hL : (1 : Nat) ≤ C.n + 1 := by omega
  have hpC : (C.pf : Int) < 2 ^ (64 * C.n + 1) := by
    have := hC.pC; have : C.pf < 2 ^ (64 * C.n + 1) := by
      unfold ICfg.pf; rw [Nat.pow_succ]; omega
    exact_mod_cast this
  have hxC : (C.x : Int) < 2 ^ (64 * C.n + 1) := by exact_mod_cast hC.xC
  obtain ⟨fodd, dbnd, bf, bg, buv, bqr, ef, eg, ed⟩ :=
    Rsa.Divstep.batch64fg (n := C.n) (k := k) (p := C.pf) (m := C.mi.toNat) (x := C.x)
      (by unfold ICfg.pf; omega) (by omega) (by omega) hpC hxC (by have := hC.n21; omega)
  -- The low words of `f` and `g`.
  have low : ∀ {j : Nat} {y : Int}, sgn (C.n + 1) (wv s.mem C.B (slot C.w j) (C.n + 1)) = y →
      ((word s.mem C.B (slot C.w j)).toNat : Int) % 2 ^ 64 = y % 2 ^ 64 := fun {j y} h => by
    rw [← h, Divstep.sgn_mod64 hL (wv_lt _ _ _ _), wv_mod64 _ _ _ hL]
    exact Int.emod_eq_of_lt (by omega) (by have := (word s.mem C.B (slot C.w j)).isLt; omega)
  unfold batch
  rw [show ([Code.block (batchHead C.iV C.iU), rowP .v16 C.iV C.iU C.iT, rowP .v17 C.iV C.iU C.iU, shrP C.iT C.iV,
      shrP C.iU C.iU, rowP .v16 C.iX₂ C.iX₁ C.iT, rowP .v17 C.iX₂ C.iX₁ C.iX₁] ++ mredP C.iT C.iM C.iX₂ ++
      mredP C.iX₁ C.iM C.iX₁) = [Code.block (batchHead C.iV C.iU)] ++ ([rowP .v16 C.iV C.iU C.iT,
      rowP .v17 C.iV C.iU C.iU, shrP C.iT C.iV, shrP C.iU C.iU] ++ ([rowP .v16 C.iX₂ C.iX₁ C.iT,
      rowP .v17 C.iX₂ C.iX₁ C.iX₁] ++ mredP C.iT C.iM C.iX₂ ++ mredP C.iX₁ C.iM C.iX₁)) by simp]
  refine wp_seqs_append ?_ ?_ ?_
  · simp
  · simp
  simp only [seqs]
  refine WP.mono (batchHead_ok hI.scr hI.x0 hI.x11 hI.x12 hC.nw hC.w24 hC.hZ hC.hV hC.hU dbnd fodd hI.d
    (low hI.f) (low hI.g)) fun s₁ ⟨l1, l2, l3, l4, l5, l6, lv, h11, h12, h15, hm₁, k₁⟩ => ?_
  have ar : ∀ j, wv s₁.mem C.B (slot C.w j) = wv s.mem C.B (slot C.w j) := fun j => by rw [hm₁]
  refine wp_seqs_append ?_ ?_ ?_
  · simp
  · simp
  refine WP.mono (fgStage_ok (hI.scr.congr k₁.wr) ((k₁.gpr .x0 (by decide)).trans hI.x0) (h11.trans hI.x11)
    (h12.trans hI.x12) hC.n1 hC.nw hC.w24 hC.hZ hC.hV hC.hU hC.hT hC.dUV.symm hC.dVT hC.dUT buv bqr l3 l4 l5 l6
    (by rw [ar]; exact hI.f) (by rw [ar]; exact hI.g) bf bg ef eg) fun s₂ ⟨f₂, g₂, fr₂, k₂, v₂⟩ => ?_
  have k12 := k₁.trans k₂
  have keepFG : ∀ {j : Nat} {L : Nat}, j ≠ C.iT → j ≠ C.iU → j ≠ C.iV → L ≤ C.w + 2 → j < 16 →
      wv s₂.mem C.B (slot C.w j) L = wv s.mem C.B (slot C.w j) L := fun {j L} a b c hL' hj => by
    rw [fr₂.wv_eq (apart3 a b c hL' (by have := hC.nw; omega) (by have := hC.nw; omega)
      (by have := hC.nw; omega)) (by have := slot_lt (w := C.w) hj; omega), ar]
  have lmi : laneOf s₂ .v18 1 = C.mi := by rw [laneOf, v₂, ← laneOf, l2, hI.mi]
  have lv' : ∀ (r : VReg) (i : Nat), r = .v16 ∨ r = .v17 → laneOf s₂ r i = laneOf s₁ r i := fun r i _ => by
    rw [laneOf, v₂]
  have hpm : wv s₂.mem C.B (slot C.w C.iM) C.n = C.p := by
    rw [keepFG hC.dMT hC.dUM.symm hC.dVM.symm (by have := hC.nw; omega) hC.hM]; exact hI.m
  refine WP.mono (abStage_ok (hI.scr.congr k12.wr) ((k12.gpr .x0 (by decide)).trans hI.x0)
    ((k₂.gpr .x11 (by decide)).trans (h11.trans hI.x11)) ((k₂.gpr .x12 (by decide)).trans (h12.trans hI.x12))
    hC.n1 hC.nw hC.w24 hC.hZ hC.hX₂ hC.hX₁ hC.hT hC.hM hC.dX.symm hC.dX₂T hC.dX₁T hC.dX₂M hC.dX₁M hC.dMT.symm hC.pC
    buv bqr (by rw [lv' _ _ (.inl rfl)]; exact l3) (by rw [lv' _ _ (.inl rfl)]; exact l4)
    (by rw [lv' _ _ (.inr rfl)]; exact l5) (by rw [lv' _ _ (.inr rfl)]; exact l6)
    (a := (C.st k).a) (b := (C.st k).b) rfl rfl)
    fun t ⟨abv, fr₃, k₃, v₃⟩ => ?_
  -- For a good `p`: `pf = p`, and `a`, `b` are those of the next batch.
  have ab₃ : C.Good → sgn (C.n + 1) (wv t.mem C.B (slot C.w C.iX₂) (C.n + 1)) = (C.st (k + 1)).a ∧
      sgn (C.n + 1) (wv t.mem C.B (slot C.w C.iX₁) (C.n + 1)) = (C.st (k + 1)).b := fun G => by
    have hpf : C.pf = C.p := by unfold ICfg.pf; have := G.1; omega
    have hm' : ((C.p : Int) * C.mi.toNat + 1) % 2 ^ 64 = 0 := by
      have := hC.hm; rw [show C.p + (1 - C.p % 2) = C.p by have := G.1; omega] at this; exact this
    have hp1 : (1 : Int) < C.p := by exact_mod_cast G.2
    obtain ⟨⟨a0, a1, b0, b1⟩, ea, eb⟩ := Rsa.Divstep.batch64ab (k := k) (x := (C.x : Int)) hp1 hm'
    obtain ⟨ra0, ra1, rb0, rb1⟩ := Divstep.invRunS_range (N := 59) (p := C.p) (m := C.mi.toNat) (x := C.x)
      (by decide) hp1 hm' (k + 1)
    have ha := hI.a G
    have hb := hI.b G
    simp only [ICfg.st] at ha hb abv ⊢
    rw [hpf] at ha hb abv ⊢
    rw [lmi] at abv
    rw [ea] at ra0 ra1; rw [eb] at rb0 rb1; rw [ea, eb]
    exact abv ⟨hm', hpm,
      by rw [keepFG hC.dX₂T hC.dUX₂.symm hC.dVX₂.symm (by have := hC.nw; omega) hC.hX₂]; exact ha,
      by rw [keepFG hC.dX₁T hC.dUX₁.symm hC.dVX₁.symm (by have := hC.nw; omega) hC.hX₁]; exact hb,
      ⟨a0, a1⟩, ⟨b0, b1⟩, ⟨ra0, ra1⟩, ⟨rb0, rb1⟩⟩
  have k13 := k12.trans k₃
  have keepAB : ∀ {j : Nat} {L : Nat}, j ≠ C.iT → j ≠ C.iX₂ → j ≠ C.iX₁ → L ≤ C.w + 2 → j < 16 →
      wv t.mem C.B (slot C.w j) L = wv s₂.mem C.B (slot C.w j) L := fun {j L} a b c hL' hj =>
    fr₃.wv_eq (apart3 a b c hL' (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      (by have := slot_lt (w := C.w) hj; omega)
  have wid : ∀ {j : Nat} {L : Nat}, (slot C.w j, 8 * (C.w + 2)) ∈ C.ranges → L ≤ 8 * (C.w + 2) →
      ∃ r' ∈ C.ranges, r'.1 ≤ slot C.w j ∧ slot C.w j + L ≤ r'.1 + r'.2 := fun {j L} h hL' =>
    ⟨_, h, Nat.le_refl _, Nat.add_le_add_left hL' _⟩
  refine ⟨⟨hI.scr.congr k13.wr, (k13.gpr .x0 (by decide)).trans hI.x0,
    (k₃.gpr .x11 (by decide)).trans ((k₂.gpr .x11 (by decide)).trans (h11.trans hI.x11)),
    (k₃.gpr .x12 (by decide)).trans ((k₂.gpr .x12 (by decide)).trans (h12.trans hI.x12)),
    by rw [keepAB hC.dVT hC.dVX₂ hC.dVX₁ (by have := hC.nw; omega) hC.hV]; exact f₂,
    by rw [keepAB hC.dUT hC.dUX₂ hC.dUX₁ (by have := hC.nw; omega) hC.hU]; exact g₂, fun G => (ab₃ G).1,
    fun G => (ab₃ G).2,
    by rw [laneOf, v₃, v₂, ← laneOf, l1]; exact congrArg _ ed.symm,
    by rw [laneOf, v₃, v₂, ← laneOf, l2, hI.mi],
    by rw [keepAB hC.dMT hC.dX₂M.symm hC.dX₁M.symm (by have := hC.nw; omega) hC.hM,
      keepFG hC.dMT hC.dUM.symm hC.dVM.symm (by have := hC.nw; omega) hC.hM]; exact hI.m, ?_,
    ((hI.keep.trans k13).mono (by decide)),
    by rw [laneOf, v₃, v₂, lv _ (by decide) (by decide) (by decide)]; exact hI.x1s,
    by rw [laneOf, v₃, v₂, lv _ (by decide) (by decide) (by decide)]; exact hI.x2s⟩, ?_⟩
  · refine (hI.frm.trans (by rw [hm₁]; exact Frm.refl _ _ _)).trans ((Frm.widen fr₂ ?_).trans (Frm.widen fr₃ ?_))
    all_goals
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> refine wid (by simp [ICfg.ranges]) (by have := hC.nw; omega)
  · rw [k₃.gpr .x15 (by decide), k₂.gpr .x15 (by decide), h15]

/-- The `3 n + 2` batches, counted by `x15`. -/
theorem batches_ok {C : ICfg} (hC : C.Ok) {s₀ s : State} (hI : LInv C s₀ 0 s)
    (h15 : s.gpr .x15 = BitVec.ofNat 64 (3 * C.n + 2)) :
    WP isa (.loop (batch C.iV C.iU C.iX₂ C.iX₁ C.iT C.iM) (.nonzero .x .x15)) s (LInv C s₀ (3 * C.n + 2)) :=
  wp_countdown (N := 3 * C.n + 2) (by have := hC.n21; omega) (by omega) (LInv C s₀)
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
    (by brun [h16, (k₁.gpr .x12 (by decide)).trans h12, shl_ofNat (show n * 2 ^ 3 < 2 ^ 64 by omega),
      RegUpd.v_write, off_add]; congr 2; omega) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h, m, v, c⟩, k⟩ => ⟨⟨h, m.trans m₁, v.trans v₁, c.trans c₁⟩, (k₁.trans k).mono (by decide)⟩

/-- `zeroTop j`: word `n` of array `j` cleared. -/
theorem zeroTop_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (j : Nat) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n) (hn : n ≤ w)
    (hw : w < 2 ^ 24) (hj : j < 16) (hZ : slot w 16 ≤ Z) :
    WP isa (.block (zeroTop j)) s fun t =>
      (t.mem = s.mem.writeW (off B (slot w j + 8 * n)) 0#64 ∧ t.v = s.v ∧ t.c = s.c) ∧ Keep [.x3, .x16] s t := by
  have sj := Nat.le_trans (slot_lt (w := w) hj) hZ
  unfold zeroTop
  refine WP.block_append_iff.mpr (WP.mono (topAt_ok j h0 h11 h12 (by omega)) fun s₁ ⟨⟨h16, m₁, v₁, c₁⟩, k₁⟩ => ?_)
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s.mem.writeW (off B (slot w j + 8 * n)) 0#64 ∧
      t.v = s₁.v ∧ t.c = s₁.c)
    (by brun [h16, (hs.congr k₁.wr).st (show slot w j + 8 * n + 8 ≤ Z by omega), m₁, RegUpd.v_write]; rfl)
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
  refine WP.block_append_iff.mpr (WP.mono (topAt_ok j h0 h11 h12 (by omega)) fun s₁ ⟨⟨h16, m₁, v₁, c₁⟩, k₁⟩ => ?_)
  refine WP.mono (WP.keep [.x3, .x7, .x15] (Q := fun t => t.gpr .x15 = 0#64 - (word s.mem B (slot w j + 8 * n) >>> 63) ∧
      t.gpr .x7 = 0 ∧ t.mem = s₁.mem ∧ t.v = s₁.v)
    (by brun [h16, (hs.congr k₁.wr).ld (show slot w j + 8 * n + 8 ≤ Z by omega), m₁, RegUpd.v_write,
      show BitVec.setWidth 64 0#16 = 0#64 from rfl]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h15, h7, m, v⟩, k⟩ => ⟨⟨h15, h7, m.trans m₁, v.trans v₁⟩, (k₁.trans k).mono (by decide)⟩

/-- The mask of a word even. -/
theorem mask_even (x : BitVec 64) : (x &&& BitVec.setWidth 64 1#16) - 1#64 = mask (decide (x.toNat % 2 = 0)) := by
  have h2 : x &&& BitVec.setWidth 64 1#16 = BitVec.ofNat 64 (x.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (BitVec.setWidth 64 1#16).toNat = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat]
    omega
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
  have sepFG := slot_apart (w := w) (a := 8) (b := 8 * (n + 1)) dFG.symm (by omega) (by omega)
  have w0 : word s₄.mem B (slot w iG) = word s.mem B (slot w iG) := by
    rw [hm₄, (writeW_outside _ B _ (by omega)).word (by omega) (by omega),
      (writeW_outside _ B _ (by omega)).word (by rcases sepFG with h | h <;> omega) (by omega)]
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x3, .x4, .x7, .x14, .x15] (Q := fun t =>
      t.gpr .x15 = mask (decide ((word s.mem B (slot w iG)).toNat % 2 = 0)) ∧ t.gpr .x7 = 0 ∧
      t.gpr .x14 = BitVec.ofNat 64 n ∧ t.c = false ∧ t.mem = s₄.mem ∧ t.v = s₄.v)
    (by brun [h8, (hs.congr k14.wr).ld (show slot w iG + 8 ≤ Z by omega), (k14.gpr .x12 (by decide)).trans h12,
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
    (by brun [h16, (hs.congr k₁.wr).st (show slot w iB + 8 ≤ Z by omega), m₁, RegUpd.v_write]; rfl)
    (by decide) (by decide) (by decide +kernel)) fun s₂ ⟨⟨m₂, v₂⟩, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  refine WP.block_append_iff.mpr (WP.mono (WP.vfix (base_ok iM .x3 ((k12.gpr .x0 (by decide)).trans h0)
    ((k12.gpr .x11 (by decide)).trans h11)) (bv _ _)) fun s₃ ⟨⟨⟨h3, m₃, _⟩, k₃⟩, v₃⟩ => ?_)
  have k13 := k12.trans k₃
  have wM : word s₃.mem B (slot w iM) = word s.mem B (slot w iM) := by
    rw [m₃, m₂, (writeW_outside _ B _ (by omega)).word (by
      rcases slot_apart (w := w) (a := 8) (b := 8) dBM.symm (by omega) (by omega) with h | h <;> omega) (by omega)]
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x3, .x4] (Q := fun t =>
      t.gpr .x3 = word s.mem B (slot w iM) ||| 1#64 ∧ t.mem = s₃.mem ∧ t.v = s₃.v)
    (by brun [h3, (hs.congr k13.wr).ld (show slot w iM + 8 ≤ Z by omega), wM, RegUpd.v_write]; rfl)
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
    rw [hm₇, (writeW_outside _ B _ (by omega)).word (by
      rcases slot_apart (w := w) (a := 8) (b := 8) dFB (by omega) (by omega) with h | h <;> omega) (by omega)]
  refine WP.mono (WP.keep [.x4, .x15] (Q := fun t => t.mem = s₇.mem.writeW (off B (slot w iF))
      (word s.mem B (slot w iF) ||| 1#64) ∧ t.v = s₇.v ∧ t.gpr .x15 = BitVec.ofNat 64 (3 * n + 2))
    (by
      unfold batchCount
      brun [h16₇, (hs.congr k17.wr).ld (show slot w iF + 8 ≤ Z by omega),
        (hs.congr k17.wr).st (show slot w iF + 8 ≤ Z by omega), wF, (k₇.gpr .x3 (by decide)).trans h3₆,
        RegUpd.v_write, (k17.gpr .x12 (by decide)).trans h12]
      simp only [off, BitVec.ofNat_add_ofNat]
      congr 1; omega) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨m₈, v₈, h15⟩, k₈⟩ =>
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
  omega

/-- Word 0 of a number or'ed with 1. -/
theorem wv_or1 (m : Mem) (B : Addr) {d k : Nat} (h : d + 8 * (k + 1) ≤ 2 ^ 64) :
    wv (m.writeW (off B d) (word m B d ||| 1#64)) B d (k + 1) =
      wv m B d (k + 1) + (1 - wv m B d (k + 1) % 2) := by
  rw [Nat.add_comm k 1, wv_add, wv_add m]
  rw [(writeW_outside m B _ (by omega)).wv (d := d + 8 * 1) (k := k) (Or.inr (by omega)) (by omega)]
  have e1 : ∀ m' : Mem, wv m' B d 1 = (word m' B d).toNat := fun m' => by simp [wv]
  rw [e1, e1, word_writeW_self, BitVec.toNat_or, BitVec.toNat_ofNat, show 1 % 2 ^ 64 = 1 from rfl, or_one_eq]
  have := (word m B d).isLt
  omega

/-- `-p⁻¹ mod 2^64` is unique. -/
theorem minv_unique {p a b : Nat} (hp : p % 2 = 1) (ha : (p * a + 1) % 2 ^ 64 = 0) (hb : (p * b + 1) % 2 ^ 64 = 0)
    (ha' : a < 2 ^ 64) (hb' : b < 2 ^ 64) : a = b := by
  have hc : Nat.Coprime (2 ^ 64) p := Nat.Coprime.pow_left _ (by
    show Nat.gcd 2 p = 1
    rw [Nat.gcd_rec, hp]; rfl)
  wlog h : a ≤ b
  · exact (this hp hb ha hb' ha' hc (by omega)).symm
  have hd : 2 ^ 64 ∣ p * (b - a) := by
    rw [Nat.mul_sub]
    have := Nat.sub_mod_eq_zero_of_mod_eq (show (p * b + 1) % 2 ^ 64 = (p * a + 1) % 2 ^ 64 by omega)
    rw [show p * b + 1 - (p * a + 1) = p * b - p * a by omega] at this
    exact Nat.dvd_of_mod_eq_zero this
  obtain ⟨k, hk⟩ := hc.dvd_of_dvd_mul_left hd
  rcases k with _ | k
  · omega
  · have : 2 ^ 64 * (k + 1) ≥ 2 ^ 64 := Nat.le_mul_of_pos_right _ (by omega)
    omega

/-- Word `n` of an array is apart from the first `n` words of each. -/
theorem top_apart {w n : Nat} (j X : Nat) (hn : n ≤ w) :
    slot w j + 8 * n ≤ slot w X + 8 * n ∨ slot w X + 8 * n + 8 ≤ slot w j := by
  by_cases h : j = X
  · subst h; exact .inl (Nat.le_refl _)
  · rcases slot_apart (w := w) (a := 8 * n) (b := 8 * n + 8) h (by omega) (by omega) with h' | h' <;> omega

/-- A prefix of a zero number is zero. -/
theorem wv_zero_prefix {m : Mem} {B : Addr} {d k j : Nat} (h : wv m B d (k + j) = 0) : wv m B d k = 0 := by
  rw [wv_add] at h; omega

/-- A signed number of `n + 1` words below `2^(64 n + 1)` is its value. -/
theorem sgn_small {n x : Nat} (hx : x < 2 ^ (64 * n + 1)) : sgn (n + 1) x = x := by
  unfold sgn
  rw [ite_eq_left (show x < 2 ^ (64 * (n + 1) - 1) from Nat.lt_of_lt_of_le hx
    (Nat.pow_le_pow_right (by decide) (by omega)))]

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
  have sepUM := slot_apart (w := C.w) (a := 8 * C.n) (b := 8 * C.n) hC.dUM (by omega) (by omega)
  have o₁ : ∀ {j : Nat}, j < 16 → wv s₁.mem C.B (slot C.w j) C.n = wv s.mem C.B (slot C.w j) C.n := fun {j} hj => by
    rw [m₁, (writeW_outside _ C.B _ (by omega)).wv (top_apart j C.iU hnw) (by have := sl _ hj; omega),
      (writeW_outside _ C.B _ (by omega)).wv (top_apart j C.iV hnw) (by have := sl _ hj; omega)]
  have k1 := k₁
  -- `g += m` if `a` is even.
  refine WP.seq (WP.mono (WP.vfix (addMIP_ok (N := C.n) (hs.congr k₁.wr) h10 h8 h5 h14 h15 hc hn1 (by omega)
    (by omega) (by omega) (by omega) (by rcases sepUM with h | h <;> omega) (.inl (Nat.le_refl _))) (by decide +kernel))
    fun s₂ ⟨⟨e₂, h5', o₂, k₂⟩, v₂⟩ => ?_)
  rw [o₁ hC.hM, o₁ hC.hU, hM, hU] at e₂
  have k12 := k₁.trans k₂
  have g7 : s₂.gpr .x7 = 0 := (k₂.gpr .x7 (by decide)).trans h7
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s₂.mem.writeW (off C.B (slot C.w C.iU + 8 * C.n))
      (BitVec.ofNat 64 s₂.c.toNat) ∧ t.v = s₂.v)
    (by brun [g7, h5', (hs.congr k12.wr).st (show slot C.w C.iU + 8 * C.n + 8 ≤ C.Z by omega), RegUpd.v_write]
        rw [zero_add64, zero_add64])
    (by decide) (by decide) (by decide +kernel)) fun s₃ ⟨⟨m₃, v₃⟩, k₃⟩ => ?_)
  have par : (word s.mem C.B (slot C.w C.iU)).toNat % 2 = a % 2 := by
    rw [← wv_mod64 _ _ _ hn1, hU, Nat.mod_mod_of_dvd _ (by decide)]
  have gU : wv s₃.mem C.B (slot C.w C.iU) (C.n + 1) = C.x := by
    rw [m₃, wv_writeW_top _ _ _ _ _ (by omega), hx, Rsa.Divstep.oddInput, BitVec.toNat_ofNat,
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
      h7' (by omega) (by have := sl _ hj; omega)) fun t ⟨z, o, k⟩ => ⟨z, by rw [m₂', m₁'] at o; exact o,
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
    Frm.of_outside (Outside.mono (o' := slot C.w C.iU) (n' := 8 * (C.w + 2)) o₂ (Nat.le_refl _) (by omega)) (by simp)
  have f3 : Frm C.B [(slot C.w C.iU, 8 * (C.w + 2)), (slot C.w C.iX₂, 8 * (C.w + 2)),
      (slot C.w C.iX₁, 8 * (C.w + 2))] s₂.mem s₃.mem := by
    rw [m₃]; exact Frm.of_outside (Outside.mono (o' := slot C.w C.iU) (n' := 8 * (C.w + 2))
      (writeW_outside _ C.B _ (by omega)) (by omega) (by omega)) (by simp)
  have f4 : Frm C.B [(slot C.w C.iU, 8 * (C.w + 2)), (slot C.w C.iX₂, 8 * (C.w + 2)),
      (slot C.w C.iX₁, 8 * (C.w + 2))] s₃.mem s₄.mem :=
    Frm.of_outside (Outside.mono (o' := slot C.w C.iX₂) (n' := 8 * (C.w + 2)) o₄ (Nat.le_refl _) (by omega)) (by simp)
  have f5 : Frm C.B [(slot C.w C.iU, 8 * (C.w + 2)), (slot C.w C.iX₂, 8 * (C.w + 2)),
      (slot C.w C.iX₁, 8 * (C.w + 2))] s₄.mem s₅.mem :=
    Frm.of_outside (Outside.mono (o' := slot C.w C.iX₁) (n' := 8 * (C.w + 2)) o₅ (Nat.le_refl _) (by omega)) (by simp)
  have f15 := ((f2.trans f3).trans f4).trans f5
  have apM := apart3 (w := C.w) (L := C.n) hC.dUM.symm hC.dX₂M.symm hC.dX₁M.symm (by omega) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _)
  have M₅ : wv s₅.mem C.B (slot C.w C.iM) C.n = C.p := by
    rw [f15.wv_eq apM (by omega), o₁ hC.hM, hM]
  refine WP.mono (initLast_ok (hs.congr k15.wr) ((k15.gpr .x0 (by decide)).trans h0)
    ((k15.gpr .x11 (by decide)).trans h11) ((k15.gpr .x12 (by decide)).trans h12) hnw hw hZ hC.hX₁ hC.hM hC.hV
    hC.dX₁M hC.dVX₁) fun t ⟨⟨m₆, l0', lmi, lv', h15'⟩, k₆⟩ => ?_
  have k16 := k15.trans k₆
  have hZ' : slot C.w 16 + C.B.toNat ≤ 2 ^ 64 := by omega
  set mid := s₅.mem.writeW (off C.B (slot C.w C.iX₁)) 1#64 with hmid
  have o₆a : Outside C.B (slot C.w C.iX₁) 8 s₅.mem mid := writeW_outside _ C.B _ (by omega)
  have sVX := slot_apart (w := C.w) (a := 8) (b := 8) hC.dVX₁ (by omega) (by omega)
  have wVm : word s₅.mem C.B (slot C.w C.iV) = word mid C.B (slot C.w C.iV) :=
    (o₆a.word (by rcases sVX with h | h <;> omega) (by omega)).symm
  rw [wVm] at m₆
  have o₆b : Outside C.B (slot C.w C.iV) 8 mid t.mem := by rw [m₆]; exact writeW_outside _ C.B _ (by omega)
  have f6 : Frm C.B C.ranges s₅.mem t.mem :=
    (Frm.of_outside (Outside.mono (o' := slot C.w C.iX₁) (n' := 8 * (C.w + 2)) o₆a (by omega) (by omega))
      (by simp [ICfg.ranges])).trans
    (Frm.of_outside (Outside.mono (o' := slot C.w C.iV) (n' := 8 * (C.w + 2)) o₆b (by omega) (by omega))
      (by simp [ICfg.ranges]))
  -- Arrays other than `f`, `a` and `b` from `s₃` on.
  have late : ∀ {j : Nat} {L : Nat}, j ≠ C.iX₂ → j ≠ C.iX₁ → j ≠ C.iV → L ≤ C.w + 2 → j < 16 →
      wv t.mem C.B (slot C.w j) L = wv s₃.mem C.B (slot C.w j) L := fun {j L} a b c hL hj => by
    rw [wv_out o₆b c.symm (by omega) hL hZ' hj, wv_out o₆a b.symm (by omega) hL hZ' hj,
      wv_out o₅ b.symm (by omega) hL hZ' hj, wv_out o₄ a.symm (by omega) hL hZ' hj]
  have sVU := slot_apart (w := C.w) (a := 8 * (C.n + 1)) (b := 8 * C.n + 8) hC.dUV.symm (by omega) (by omega)
  have sVU0 := slot_apart (w := C.w) (a := 8 * (C.n + 1)) (b := 8 * C.n) hC.dUV.symm (by omega) (by omega)
  have V21 : wv s₂.mem C.B (slot C.w C.iV) (C.n + 1) = wv s₁.mem C.B (slot C.w C.iV) (C.n + 1) :=
    o₂.wv (by rcases sVU0 with h | h <;> omega) (by omega)
  -- `f = m` before its low bit is set.
  have fV₃ : wv s₃.mem C.B (slot C.w C.iV) (C.n + 1) = C.p := by
    rw [m₃, (writeW_outside _ C.B _ (by omega)).wv
      (by rcases sVU with h | h <;> omega) (by omega), V21, m₁,
      (writeW_outside _ C.B _ (by omega)).wv (by rcases sVU with h | h <;> omega) (by omega),
      wv_writeW_top _ _ _ _ _ (by omega), hV]
    rfl
  have fVm : wv mid C.B (slot C.w C.iV) (C.n + 1) = C.p := by
    rw [wv_out o₆a hC.dVX₁.symm (by omega) (by omega) hZ' hC.hV,
      wv_out o₅ hC.dVX₁.symm (by omega) (by omega) hZ' hC.hV, wv_out o₄ hC.dVX₂.symm (by omega) (by omega) hZ' hC.hV,
      fV₃]
  have fV : wv t.mem C.B (slot C.w C.iV) (C.n + 1) = C.pf := by
    rw [m₆, wv_or1 _ _ (by omega), fVm]; rfl
  -- `g`.
  have gU' : wv t.mem C.B (slot C.w C.iU) (C.n + 1) = C.x := by
    rw [late hC.dUX₂ hC.dUX₁ hC.dUV (by omega) hC.hU, gU]
  have aX : wv t.mem C.B (slot C.w C.iX₂) (C.n + 1) = 0 := by
    rw [wv_out o₆b hC.dVX₂ (by omega) (by omega) hZ' hC.hX₂, wv_out o₆a hC.dX (by omega) (by omega) hZ' hC.hX₂,
      wv_out o₅ hC.dX (by omega) (by omega) hZ' hC.hX₂]
    exact wv_zero_prefix (j := 1) z₄
  have bX : wv t.mem C.B (slot C.w C.iX₁) (C.n + 1) = 1 := by
    rw [wv_out o₆b hC.dVX₁ (by omega) (by omega) hZ' hC.hX₁]
    have e := wv_add mid C.B (slot C.w C.iX₁) 1 C.n
    have z := wv_add s₅.mem C.B (slot C.w C.iX₁) 1 (C.n + 1)
    rw [show 1 + (C.n + 1) = C.n + 2 by omega, z₅] at z
    have z' : wv s₅.mem C.B (slot C.w C.iX₁ + 8 * 1) C.n = 0 := wv_zero_prefix (j := 1) (by omega)
    rw [Nat.add_comm 1 C.n] at e
    rw [e, hmid, (writeW_outside _ C.B _ (by omega)).wv (d := slot C.w C.iX₁ + 8 * 1) (k := C.n) (by omega) (by omega), z']
    simp only [wv, Nat.mul_zero, Nat.add_zero, word_writeW_self, Nat.zero_add, Nat.pow_zero, Nat.one_mul]; rfl
  have hpN : C.pf < 2 ^ (64 * C.n + 1) := by have := hC.pC; unfold ICfg.pf; rw [Nat.pow_succ]; omega
  have v15 : t.v .v19 = s₁.v .v19 := by rw [lv' _ (by decide), v₅, v₄, v₃, v₂]
  have hw0 : (word s₅.mem C.B (slot C.w C.iM) ||| 1#64).toNat = C.pf % 2 ^ 64 := by
    rw [BitVec.toNat_or, BitVec.toNat_ofNat, show 1 % 2 ^ 64 = 1 from rfl, or_one_eq, ← wv_mod64 _ _ _ hn1, M₅]
    have := hC.pC
    unfold ICfg.pf
    have h64 : C.p % 2 ^ 64 % 2 = C.p % 2 := Nat.mod_mod_of_dvd _ (by decide)
    have : C.p % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
    rw [h64]
    omega
  refine ⟨⟨hs.congr k16.wr, (k16.gpr .x0 (by decide)).trans h0, (k16.gpr .x11 (by decide)).trans h11,
    (k16.gpr .x12 (by decide)).trans h12,
    by rw [fV, sgn_small hpN]; simp only [ICfg.st, Divstep.invRunS],
    by rw [gU', sgn_small hC.xC]; simp only [ICfg.st, Divstep.invRunS],
    fun _ => by rw [aX, sgn_small (Nat.two_pow_pos (64 * C.n + 1))]; simp only [ICfg.st, Divstep.invRunS]; rfl,
    fun _ => by rw [bX, sgn_small (Nat.one_lt_two_pow (by omega))]; simp only [ICfg.st, Divstep.invRunS]; rfl,
    by rw [l0']; simp only [ICfg.st, Divstep.invRunS]; decide, ?_, ?_, ?_, k16.mono (by decide),
    by rw [laneOf, v15, ← laneOf, l0], by rw [laneOf, v15, ← laneOf, l1]⟩, h15'⟩
  · apply BitVec.eq_of_toNat_eq
    refine minv_unique (p := C.pf % 2 ^ 64) (by unfold ICfg.pf; omega) (by rw [← hw0]; exact lmi) ?_
      (BitVec.isLt _) (BitVec.isLt _)
    have := hC.hm
    have h' : (C.pf * C.mi.toNat + 1) % 2 ^ 64 = 0 := by unfold ICfg.pf; exact_mod_cast this
    rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]; exact h'
  · rw [wv_out o₆b hC.dVM (by omega) (by omega) hZ' hC.hM, wv_out o₆a hC.dX₁M (by omega) (by omega) hZ' hC.hM,
      M₅]
  · have f01 : Frm C.B C.ranges s.mem s₁.mem := by
      rw [m₁]
      exact (Frm.of_outside (Outside.mono (o' := slot C.w C.iV) (n' := 8 * (C.w + 2))
        (writeW_outside _ C.B _ (by omega)) (by omega) (by omega)) (by simp [ICfg.ranges])).trans
        (Frm.of_outside (Outside.mono (o' := slot C.w C.iU) (n' := 8 * (C.w + 2))
        (writeW_outside _ C.B _ (by omega)) (by omega) (by omega)) (by simp [ICfg.ranges]))
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
  refine wp_countdown (N := L) (by omega) (by omega) (CnegInv s B Z eX neg) (fun j hj t hI _ => ?_) h0 h14
  have t15 : t.gpr .x15 = mask neg := (hI.keep.gpr .x15 (by decide)).trans h15
  have t7 : t.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans h7
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x16] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (eX + 8 * j)) ((word t.mem B (eX + 8 * j) ^^^ mask neg) + 0 +
        BitVec.ofNat 64 t.c.toNat) ∧
      t₁.c = decide (2 ^ 64 ≤ (word t.mem B (eX + 8 * j) ^^^ mask neg).toNat + (0 : BitVec 64).toNat + t.c.toNat) ∧
      t₁.gpr .x16 = off B (eX + 8 * j + 8))
    (by unfold cnegBody; brun [hI.x16, t15, t7, hI.scr.ld (show eX + 8 * j + 8 ≤ Z by omega),
      hI.scr.st (show eX + 8 * j + 8 ≤ Z by omega)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, hc', h16'⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14', hm', hc''⟩, k'⟩ => ⟨?_, by rw [h14', k₁.gpr .x14 (by decide)]⟩
  have hx : word t.mem B (eX + 8 * j) = word s.mem B (eX + 8 * j) := hI.out.word (by omega) (by omega)
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16', Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega), hc'', hc']
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
      rw [Nat.mul_add]; omega
    · simp only [ite_true, Bool.toNat_true] at hval ⊢
      have e1 : P * (2 ^ 64 - 1 - (word s.mem B (eX + 8 * j)).toNat + t.c.toNat) =
          P * 2 ^ 64 - P - P * (word s.mem B (eX + 8 * j)).toNat + P * t.c.toNat := by
        rw [Nat.mul_add, Nat.mul_sub, Nat.mul_sub, Nat.mul_one]
      have e2 : P * (word s.mem B (eX + 8 * j)).toNat ≤ P * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_sub, Nat.mul_one] at e2
      have e3 : P ≤ P * 2 ^ 64 := Nat.le_mul_of_pos_right _ (by decide)
      rw [e1]; omega

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
    ((k12.gpr .x15 (by decide)).trans h15) h7 hc (by omega) (by omega) (by omega)) fun t hI => ⟨?_, ?_, ?_⟩
  · have := hI.val; rw [m₂, m₁] at this; exact this
  · rw [← m₁, ← m₂]; exact hI.out
  · exact (k12.trans hI.keep).mono (by decide)

/-- The sign mask of word `n` as a `mask`. -/
theorem zero_add64' (x y : BitVec 64) : x + 0 + y = x + y := by rw [add_zero64]

theorem signMask_mask (x : BitVec 64) : 0#64 - (x >>> 63) = mask (decide (2 ^ 63 ≤ x.toNat)) := by
  rw [Divstep.signMask_eq]
  by_cases h : x.toNat < 2 ^ 63
  · rw [ite_eq_left h, decide_eq_false (by omega)]; rfl
  · rw [ite_eq_right h, decide_eq_true (by omega)]; rfl

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
  have sepAM := slot_apart (w := w) (a := 8 * n) (b := 8 * n) dAM (by omega) (by omega)
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
    (by rw [c₅, c₄, c₃, hc]) hn1 (by omega) (by omega) (by omega) (by omega) (by rcases sepAM with h | h <;> omega)
    (.inl (Nat.le_refl _))) fun s₆ ⟨e₆, h5', o₆, k₆⟩ => ?_)
  have k16 := k15.trans k₆
  have g7 : s₆.gpr .x7 = 0 := ((((k₂.trans k₃).trans k₄).trans k₅).trans k₆ |>.gpr .x7 (by decide)).trans h7
  have An : wv s₅.mem B (slot w iA) n = wv s.mem B (slot w iA) n := by rw [hm₅]
  have Mn : wv s₅.mem B (slot w iM) n = wv s.mem B (slot w iM) n := by rw [hm₅]
  rw [An, Mn] at e₆
  have top₆ : word s₆.mem B (slot w iA + 8 * n) = word s.mem B (slot w iA + 8 * n) := by
    rw [o₆.word (by omega) (by omega), hm₅]
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s₆.mem.writeW (off B (slot w iA + 8 * n))
      (word s.mem B (slot w iA + 8 * n) + 0 + BitVec.ofNat 64 s₆.c.toNat))
    (by brun [h5', g7, (hs.congr k16.wr).ld (show slot w iA + 8 * n + 8 ≤ Z by omega),
      (hs.congr k16.wr).st (show slot w iA + 8 * n + 8 ≤ Z by omega), top₆]) (by decide) (by decide)
    (by decide +kernel)) fun t ⟨hm, k⟩ => ⟨?_, ?_, (k16.trans k).mono (by decide)⟩
  · rw [hm, wv_writeW_top _ _ _ _ _ (by omega), zero_add64', wv]
    have hW := wv_lt s₆.mem B (slot w iA) n
    have ad : (word s.mem B (slot w iA + 8 * n) + BitVec.ofNat 64 s₆.c.toNat).toNat =
        ((word s.mem B (slot w iA + 8 * n)).toNat + s₆.c.toNat) % 2 ^ 64 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show s₆.c.toNat < 2 ^ 64 by
        have := Bool.toNat_le s₆.c; omega)]
    rw [ad, show 64 * (n + 1) = 64 * n + 64 by omega, Nat.pow_add,
      ← add_mul_mod_mul (Q := 2 ^ 64) hW]
    congr 1
    simp only [decide_eq_true_eq] at e₆
    rw [Nat.mul_add, ← Nat.add_assoc, Nat.add_right_comm, e₆]
    ac_rfl
  · rw [hm, ← hm₅]
    intro x hx
    rw [writeW_outside _ B _ (by omega) x (by omega)]
    exact Outside.mono (o' := slot w iA) (n' := 8 * (n + 1)) o₆ (Nat.le_refl _) (by omega) x hx
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
  have pAT := slot_apart (w := w) (a := 8 * (n + 1)) (b := 8 * n) dAT (by omega) (by omega)
  have pMT := slot_apart (w := w) (a := 8 * n) (b := 8 * n) dMT (by omega) (by omega)
  have pAM := slot_apart (w := w) (a := 8 * (n + 1)) (b := 8 * n) dAM (by omega) (by omega)
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
    hn1 (by omega) (by omega) (by omega) (by omega) (by rcases pAT with h | h <;> omega)
    (by rcases pMT with h | h <;> omega)) fun s₆ ⟨c, hc, hD, o₆, k₆⟩ => ?_)
  have k16 := k15.trans k₆
  refine WP.seq (WP.mono (selectAccIP_ok (w := n) (hs.congr k16.wr)
    ((k₆.gpr .x8 (by decide)).trans ((k₅.gpr .x8 (by decide)).trans ((k₄.gpr .x8 (by decide)).trans
      ((k₃.gpr .x8 (by decide)).trans ((k₂.gpr .x8 (by decide)).trans h8)))))
    ((k₆.gpr .x6 (by decide)).trans ((k₅.gpr .x6 (by decide)).trans ((k₄.gpr .x6 (by decide)).trans h6)))
    ((k₆.gpr .x5 (by decide)).trans ((k₅.gpr .x5 (by decide)).trans h5)) ((k16.gpr .x12 (by decide)).trans h12)
    hc hn1 (by omega) (by omega) (by omega) (by omega) (.inl (Nat.le_refl _)) (by rcases pAT with h | h <;> omega))
    fun s₇ ⟨hv₇, o₇, k₇⟩ => ?_)
  have k17 := k16.trans k₇
  refine WP.mono (zeroTop_ok (hs.congr k17.wr) iA ((k17.gpr .x0 (by decide)).trans h0)
    ((k17.gpr .x11 (by decide)).trans h11) ((k17.gpr .x12 (by decide)).trans h12) hn hw hA hZ)
    fun t ⟨⟨m₈, _, _⟩, k₈⟩ => ⟨fun hlt => ?_, ?_, (k17.trans k₈).mono (by decide)⟩
  · have A6 : wv s₆.mem B (slot w iA) n = wv s.mem B (slot w iA) n := by
      rw [o₆.wv (by rcases pAT with h | h <;> omega) (by omega), hm₅]
    have Aw : word s₆.mem B (slot w iA + 8 * n) = word s.mem B (slot w iA + 8 * n) := by
      rw [o₆.word (by rcases pAT with h | h <;> omega) (by omega), hm₅]
    rw [hm₅] at hD
    have hp := wv_lt s.mem B (slot w iM) n
    have cs := VG.Proof.Bignum.csub_result (Tl := wv s.mem B (slot w iA) n)
      (Tw := (word s.mem B (slot w iA + 8 * n)).toNat) (Tw1 := 0) (D := wv s₆.mem B (slot w iT) n)
      (m := wv s.mem B (slot w iM) n) (R := 2 ^ (64 * n)) (c := c.toNat) hp (wv_lt _ _ _ _) (Bool.toNat_le c)
      (wv_lt _ _ _ _) (by rw [Nat.mul_zero, Nat.add_zero]; rw [wv] at hlt; omega) hD
    rw [hm₅] at hv₇
    rw [m₈, wv_writeW_top _ _ _ _ _ (by omega), hv₇, A6]
    rw [Nat.mul_zero, Nat.add_zero] at cs
    rw [wv, ← cs]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
    by_cases h : (word s.mem B (slot w iA + 8 * n)).toNat < c.toNat <;> simp [h]
  · have f6 : Frm B [(slot w iA, 8 * (n + 1)), (slot w iT, 8 * n)] s₅.mem s₆.mem := Frm.of_outside o₆ (by simp)
    have f7 : Frm B [(slot w iA, 8 * (n + 1)), (slot w iT, 8 * n)] s₆.mem s₇.mem :=
      Frm.of_outside (Outside.mono (o' := slot w iA) (n' := 8 * (n + 1)) o₇ (Nat.le_refl _) (by omega)) (by simp)
    have f8 : Frm B [(slot w iA, 8 * (n + 1)), (slot w iT, 8 * n)] s₇.mem t.mem := by
      rw [m₈]; exact Frm.of_outside (Outside.mono (o' := slot w iA) (n' := 8 * (n + 1))
        (writeW_outside _ B _ (by omega)) (by omega) (by omega)) (by simp)
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
    fun h => slot_apart (w := w) h (by omega) (by omega)
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
  refine WP.seq (WP.mono (wp_countdown (N := n) (by omega) (by omega)
    (DblInv s₅ B Z (slot w iT) (slot w iA))
    (fun j hj t hI _ => dblStep_ok (w := n) (by omega) (by omega)
      (by rcases pTA with h | h <;> omega) hj hI) h0' h14) fun s₆ hI => ?_)
  have hval := hI.val
  have s₆7 : s₆.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans h7
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun t =>
      t.mem = s₆.mem.writeW (off B (slot w iT + 8 * n)) (BitVec.ofNat 64 s₆.c.toNat))
    (by brun [hI.x16, s₆7, hI.scr.st (show slot w iT + 8 * n + 8 ≤ Z by omega)]
        simp only [add_zero64, zero_add64])
    (by decide) (by decide) (by decide +kernel)) fun s₇ ⟨hm₇, k₇⟩ => ?_)
  have hs₇ := hI.scr.congr k₇.wr
  have k57 := hI.keep.trans k₇
  have o7 : Outside B (slot w iT) (8 * (n + 1)) s₅.mem s₇.mem := by
    rw [hm₇]
    intro x hx
    rw [writeW_outside s₆.mem B _ (by omega) x (by omega)]
    exact hI.out x (by omega)
  rw [hm₅] at o7
  have fM : wv s₇.mem B (slot w iM) n = wv s.mem B (slot w iM) n :=
    o7.wv (by rcases pMT with h | h <;> omega) (by omega)
  have hTl : wv s₇.mem B (slot w iT) n = wv s₆.mem B (slot w iT) n := by
    rw [hm₇]; exact (writeW_outside s₆.mem B _ (by omega)).wv (Or.inl (by omega)) (by omega)
  have hTw : (word s₇.mem B (slot w iT + 8 * n)).toNat = s₆.c.toNat := by
    rw [hm₇, word_writeW_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Bool.toNat_le s₆.c; omega)]
  refine WP.seq (WP.mono (subMod_ok (w := n) hs₇ ((k57.gpr .x8 (by decide)).trans e8)
    ((k57.gpr .x10 (by decide)).trans e10) ((k57.gpr .x6 (by decide)).trans e6)
    ((k57.gpr .x12 (by decide)).trans e12) ((k57.gpr .x7 (by decide)).trans h7) hn1 (by omega) (by omega)
    (by omega) (by omega) (by rcases pTS with h | h <;> omega) (by rcases pMS with h | h <;> omega))
    fun s₈ ⟨c', hc₈, hD, o₈, k₈⟩ => ?_)
  have k58 := k57.trans k₈
  refine WP.mono (selectAcc_ok (w := n) (hs₇.congr k₈.wr) ((k58.gpr .x8 (by decide)).trans e8)
    ((k58.gpr .x6 (by decide)).trans e6) ((k58.gpr .x5 (by decide)).trans e5)
    ((k58.gpr .x12 (by decide)).trans e12) hc₈ hn1 (by omega) (by omega) (by omega) (by omega)
    (by rcases pTA with h | h <;> omega) (by rcases pAS with h | h <;> omega)) fun t ⟨hv', hot, k₉⟩ => ?_
  have hT₈ : wv s₈.mem B (slot w iT) n = wv s₇.mem B (slot w iT) n :=
    o₈.wv (by rcases pTS with h | h <;> omega) (by omega)
  rw [fM] at hD
  have fA : wv s₅.mem B (slot w iA) n = wv s.mem B (slot w iA) n := by rw [hm₅]
  rw [fA] at hval
  refine ⟨fun hlt => ?_, ?_, ((k15.trans k58).trans k₉).mono (by decide)⟩
  · rw [hv', hT₈, hTw]
    have := VG.Proof.Bignum.csub_result (Tl := wv s₇.mem B (slot w iT) n) (Tw := s₆.c.toNat) (Tw1 := 0)
      (D := wv s₈.mem B (slot w iS) n) (m := wv s.mem B (slot w iM) n) (R := 2 ^ (64 * n))
      (c := c'.toNat) (wv_lt s.mem B (slot w iM) n) (wv_lt _ _ _ _) (Bool.toNat_le c')
      (wv_lt _ _ _ _) (by rw [hTl, Nat.mul_zero, Nat.add_zero]; omega) hD
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
    · exact slot_apart (w := w) dAM.symm (by omega) (by omega)
    · exact slot_apart (w := w) dMT (by omega) (by omega)
    · exact slot_apart (w := w) dMS (by omega) (by omega)
  refine wp_countdown (N := K) hK' hK (DInv s B Z w n iA iM iT iS) (fun j _ t hI _ => ?_)
    ⟨hs, h0, h11, h12, fun h => by rw [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt h], Frm.refl _ _ _,
      Keep.refl _ _, rfl⟩ h15
  have fM : wv t.mem B (slot w iM) n = wv s.mem B (slot w iM) n := hI.frm.wv_eq apM (by omega)
  refine WP.seq (WP.mono (dblP_ok hI.scr hI.x0 hI.x11 hI.x12 hn1 hn hw hZ hA hM hT hS dAM dAT dAS dMT dMS dTS)
    fun t₁ ⟨v₁, f₁, k₁, vv₁⟩ => WP.mono (WP.vfix (dec_ok t₁ .x15) (by decide)) fun t' ⟨⟨⟨c', m', _⟩, k'⟩, vv'⟩ =>
      ⟨?_, ?_⟩)
  · have k1' := k₁.trans k'
    refine ⟨hI.scr.congr k1'.wr, (k1'.gpr .x0 (by decide)).trans hI.x0, (k1'.gpr .x11 (by decide)).trans hI.x11,
      (k1'.gpr .x12 (by decide)).trans hI.x12, fun h => ?_, ?_, (hI.keep.trans k1').mono (by decide), ?_⟩
    · have hv := hI.val h
      have hlt : wv t.mem B (slot w iA) n < wv t.mem B (slot w iM) n := by
        rw [hv, fM]; exact Nat.mod_lt _ (by omega)
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
      rw [← Nat.pow_add, show 64 * n + 64 = 64 * (n + 1) by omega]
    have := Nat.mul_le_mul_left (2 ^ (64 * n)) (show top + 1 ≤ 2 ^ 64 by omega)
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  refine Divstep.sgn_addIfNeg (by omega) hXR ?_ r₀ r₁
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
  have ht : top < 2 ^ 63 := Nat.lt_of_not_le fun h' => absurd (hiff.mpr h') (by omega)
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
      omega
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
  have hZ' : slot C.w 16 + C.B.toNat ≤ 2 ^ 64 := by omega
  have sl : ∀ j < 16, slot C.w j + 8 * (C.w + 2) ≤ C.Z := fun j hj => Nat.le_trans (slot_lt (w := C.w) hj) hZ
  have sV := sl _ hC.hV; have sX₂ := sl _ hC.hX₂; have sM := sl _ hC.hM
  have rg : ∀ {j : Nat} {len : Nat}, (slot C.w j, 8 * (C.w + 2)) ∈ C.ranges → len ≤ 8 * (C.w + 2) →
      ∀ {m m' : Mem}, Outside C.B (slot C.w j) len m m' → Frm C.B C.ranges m m' := fun {j len} hr hl {m m'} o =>
    Frm.of_outside (Outside.mono (o' := slot C.w j) (n' := 8 * (C.w + 2)) o (Nat.le_refl _) (by omega)) hr
  have rV : (slot C.w C.iV, 8 * (C.w + 2)) ∈ C.ranges := by simp [ICfg.ranges]
  have rX₂ : (slot C.w C.iX₂, 8 * (C.w + 2)) ∈ C.ranges := by simp [ICfg.ranges]
  have rT : (slot C.w C.iT, 8 * (C.w + 2)) ∈ C.ranges := by simp [ICfg.ranges]
  have rU : (slot C.w C.iU, 8 * (C.w + 2)) ∈ C.ranges := by simp [ICfg.ranges]
  unfold batchFinish
  rw [show ([Code.block (signMask C.iV), cnegP C.iV, cnegP C.iX₂] ++ addIfNeg C.iX₂ C.iM ++ addIfNeg C.iX₂ C.iM ++
      csubP C.iX₂ C.iM C.iT ++ [.seq (.block dblCount) (.loop (.seq (dblP C.iX₂ C.iM C.iT C.iU)
        (.block [.subImm .x .x15 .x15 1])) (.nonzero .x .x15)), .block [.umov .x .x1 .v19 0, .umov .x .x2 .v19 1]] :
      List (Prog isa)) = [Code.block (signMask C.iV), cnegP C.iV, cnegP C.iX₂] ++ (addIfNeg C.iX₂ C.iM ++
      (addIfNeg C.iX₂ C.iM ++ (csubP C.iX₂ C.iM C.iT ++ [.seq (.block dblCount) (.loop (.seq (dblP C.iX₂ C.iM C.iT C.iU)
        (.block [.subImm .x .x15 .x15 1])) (.nonzero .x .x15)), .block [.umov .x .x1 .v19 0, .umov .x .x2 .v19 1]])))
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
        brun [(k06.gpr .x12 (by decide)).trans hI.x12, shl_ofNat (show C.n * 2 ^ 4 < 2 ^ 64 by omega)]
        apply BitVec.eq_of_toNat_eq
        have := hC.n21
        simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega)
      (by decide) (by decide) (by decide +kernel)) (by decide +kernel))
    fun s₇ ⟨⟨⟨h15₇, m₇⟩, k₇⟩, v₇⟩ => WP.mono (dblLoop_ok (K := 15 * C.n + 10) (sc₆.congr k₇.wr)
      ((k₇.gpr .x0 (by decide)).trans ((k06.gpr .x0 (by decide)).trans hI.x0))
      ((k₇.gpr .x11 (by decide)).trans ((k06.gpr .x11 (by decide)).trans hI.x11))
      ((k₇.gpr .x12 (by decide)).trans ((k06.gpr .x12 (by decide)).trans hI.x12)) hn1 hnw hw hZ hC.hX₂ hC.hM hC.hT
      hC.hU hC.dX₂M hC.dX₂T hC.dUX₂.symm hC.dMT hC.dUM.symm hC.dUT.symm (by omega) (by omega) h15₇)
    fun s₈ hD => ?_))
  have k07 := k06.trans k₇
  have k08 := k07.trans hD.keep
  -- `x1`, `x2` back.
  refine WP.mono (WP.keep [.x1, .x2] (Q := fun t => t.gpr .x1 = (s₈.v .v19).extractLsb' 0 64 ∧
      t.gpr .x2 = (s₈.v .v19).extractLsb' 64 64 ∧ t.mem = s₈.mem)
    (by brun [exec_umov_x, RegUpd.v_write, Nat.mul_zero, Nat.mul_one]) (by decide) (by decide) (by decide +kernel))
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
      · exact ⟨_, rX₂, Nat.le_refl _, by dsimp only; omega⟩
      · exact ⟨_, rT, Nat.le_refl _, by dsimp only; omega⟩
    have w8 : Frm C.B C.ranges s₇.mem s₈.mem := Frm.widen hD.frm fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, rX₂, Nat.le_refl _, by dsimp only; omega⟩
      · exact ⟨_, rT, Nat.le_refl _, by dsimp only; omega⟩
      · exact ⟨_, rU, Nat.le_refl _, by dsimp only; omega⟩
    rw [mt]
    refine hI.frm.trans ?_
    rw [m₁] at o₂
    rw [m₇] at w8
    exact (((((rg rV (by omega) o₂).trans (rg rX₂ (by omega) o₃)).trans (rg rX₂ (by omega) o₄)).trans
      (rg rX₂ (by omega) o₅)).trans w6).trans w8
  · intro G a ha hx
    have hL : 1 ≤ C.n + 1 := by omega
    have hpf : C.pf = C.p := by unfold ICfg.pf; have := G.1; omega
    have hm' : ((C.p : Int) * C.mi.toNat + 1) % 2 ^ 64 = 0 := by
      have := hC.hm; rw [show C.p + (1 - C.p % 2) = C.p by have := G.1; omega] at this; exact this
    have hp1 : (1 : Int) < C.p := by exact_mod_cast G.2
    have est : C.st (3 * C.n + 2) =
        Divstep.invRunS 59 C.p C.mi.toNat (Rsa.Divstep.oddInput C.p a) (3 * C.n + 2) := by
      unfold ICfg.st; rw [hpf, hx]
    obtain ⟨-, rf0, rr⟩ := Rsa.Divstep.invRunS59_result (mi := C.mi.toNat) G.1 G.2 hm' hC.pC ha
    obtain ⟨ra0, ra1, -, -⟩ := Divstep.invRunS_range (N := 59) (p := C.p) (m := C.mi.toNat)
      (x := Rsa.Divstep.oddInput C.p a) (by decide) hp1 hm' (3 * C.n + 2)
    rw [← est] at rf0 rr ra0 ra1
    have hf := hI.f
    have hav := hI.a G
    set f := (C.st (3 * C.n + 2)).f with hfdef
    set av := (C.st (3 * C.n + 2)).a with hadef
    have gp : Nat.gcd C.p a ≤ C.p := Nat.gcd_le_left _ (by omega)
    have pC := hC.pC
    have half : (2 : Int) ^ (64 * C.n) * 2 ≤ 2 ^ (64 * (C.n + 1) - 1) := by
      have : 2 ^ (64 * C.n) * 2 ≤ 2 ^ (64 * (C.n + 1) - 1) := by
        rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) (by omega)
      exact_mod_cast this
    have pC' : (C.p : Int) < 2 ^ (64 * C.n) := by exact_mod_cast pC
    have fabs : |f| = (Nat.gcd C.p a : Int) := by rw [← Int.natCast_natAbs, rf0]
    have fabs' : |f| < 2 ^ (64 * C.n) := by rw [fabs]; omega
    -- Memory between the stages.
    have M₀ := hI.m
    have wsucc : ∀ (m : Mem) (j : Nat), wv m C.B (slot C.w j) (C.n + 1) =
        wv m C.B (slot C.w j) C.n + 2 ^ (64 * C.n) * (word m C.B (slot C.w j + 8 * C.n)).toNat := fun m j => by
      rw [wv]
    have M₃ : wv s₃.mem C.B (slot C.w C.iM) C.n = C.p := by
      rw [wv_out o₃ hC.dX₂M (by omega) (by omega) hZ' hC.hM, wv_out o₂ hC.dVM (by omega) (by omega) hZ' hC.hM, m₁, M₀]
    have M₄ : wv s₄.mem C.B (slot C.w C.iM) C.n = C.p := by
      rw [wv_out o₄ hC.dX₂M (by omega) (by omega) hZ' hC.hM, M₃]
    have M₅ : wv s₅.mem C.B (slot C.w C.iM) C.n = C.p := by
      rw [wv_out o₅ hC.dX₂M (by omega) (by omega) hZ' hC.hM, M₄]
    have apM6 : ∀ r ∈ [(slot C.w C.iX₂, 8 * (C.n + 1)), (slot C.w C.iT, 8 * C.n)],
        slot C.w C.iM + 8 * C.n ≤ r.1 ∨ r.1 + r.2 ≤ slot C.w C.iM := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slot_apart (w := C.w) hC.dX₂M.symm (by omega) (by omega)
      · exact slot_apart (w := C.w) hC.dMT (by omega) (by omega)
    have M₇ : wv s₇.mem C.B (slot C.w C.iM) C.n = C.p := by
      rw [m₇, f₆.wv_eq apM6 (by omega), M₅]
    -- `|f|` in `v`.
    have hneg : (2 ^ 63 ≤ (word s.mem C.B (slot C.w C.iV + 8 * C.n)).toNat) ↔ f < 0 := by
      rw [← hf, wsucc]
      exact (Divstep.sgn_neg_iff (wv_lt _ _ _ _) (BitVec.isLt _)).symm
    rw [m₁] at e₂
    have V₂ := Divstep.sgn_cneg hL (wv_lt _ _ _ _) (wv_lt _ _ _ _) (by rw [hf]; omega) e₂
    rw [hf] at V₂
    have V₂' : sgn (C.n + 1) (wv s₂.mem C.B (slot C.w C.iV) (C.n + 1)) = |f| := by
      rw [V₂]
      by_cases h : f < 0
      · rw [ite_eq_left (decide_eq_true (hneg.mpr h)), abs_of_neg h]
      · rw [ite_eq_right (by simp only [decide_eq_true_eq]; exact fun h' => h (hneg.mp h')), abs_of_nonneg (by omega)]
    obtain ⟨-, V₂n⟩ := small_of_sgn (wsucc _ _) (wv_lt _ _ _ _) (BitVec.isLt _) V₂' (abs_nonneg _) fabs'
    have apV6 : ∀ r ∈ [(slot C.w C.iX₂, 8 * (C.n + 1)), (slot C.w C.iT, 8 * C.n)],
        slot C.w C.iV + 8 * C.n ≤ r.1 ∨ r.1 + r.2 ≤ slot C.w C.iV := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slot_apart (w := C.w) hC.dVX₂ (by omega) (by omega)
      · exact slot_apart (w := C.w) hC.dVT (by omega) (by omega)
    have apV8 : ∀ r ∈ [(slot C.w C.iX₂, 8 * C.n), (slot C.w C.iT, 8 * (C.n + 1)), (slot C.w C.iU, 8 * C.n)],
        slot C.w C.iV + 8 * C.n ≤ r.1 ∨ r.1 + r.2 ≤ slot C.w C.iV := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact slot_apart (w := C.w) hC.dVX₂ (by omega) (by omega)
      · exact slot_apart (w := C.w) hC.dVT (by omega) (by omega)
      · exact slot_apart (w := C.w) hC.dUV.symm (by omega) (by omega)
    have Vt : wv t.mem C.B (slot C.w C.iV) C.n = Nat.gcd C.p a := by
      rw [mt, hD.frm.wv_eq apV8 (by omega), m₇, f₆.wv_eq apV6 (by omega),
        wv_out o₅ hC.dVX₂.symm (by omega) (by omega) hZ' hC.hV, wv_out o₄ hC.dVX₂.symm (by omega) (by omega) hZ' hC.hV,
        wv_out o₃ hC.dVX₂.symm (by omega) (by omega) hZ' hC.hV]
      have := V₂n.trans fabs
      exact_mod_cast this
    refine ⟨Vt, ?_⟩
    -- `±a` in `x₂`.
    have A₂ : wv s₂.mem C.B (slot C.w C.iX₂) (C.n + 1) = wv s.mem C.B (slot C.w C.iX₂) (C.n + 1) := by
      rw [wv_out o₂ hC.dVX₂ (by omega) (by omega) hZ' hC.hX₂, m₁]
    rw [A₂] at e₃
    have A₃ := Divstep.sgn_cneg hL (wv_lt _ _ _ _) (wv_lt _ _ _ _) (by rw [hav]; omega) e₃
    rw [hav] at A₃
    set b0 := if f < 0 then -av else av with hb0
    have A₃' : sgn (C.n + 1) (wv s₃.mem C.B (slot C.w C.iX₂) (C.n + 1)) = b0 := by
      rw [A₃]
      by_cases h : f < 0
      · rw [ite_eq_left (decide_eq_true (hneg.mpr h)), hb0, ite_eq_left h]
      · rw [ite_eq_right (by simp only [decide_eq_true_eq]; exact fun h' => h (hneg.mp h')), hb0, ite_eq_right h]
    have b0r : -2 * (C.p : Int) < b0 ∧ b0 < 2 * C.p := by
      rw [hb0]; split <;> omega
    -- `p` added if negative, twice.
    rw [M₃] at e₄
    have A₄ := addIfNeg_step (wsucc _ _) (wv_lt _ _ _ _) (BitVec.isLt _) e₄ (by rw [A₃']; split <;> omega)
      (by rw [A₃']; split <;> omega)
    rw [A₃'] at A₄
    set b1 := b0 + if b0 < 0 then (C.p : Int) else 0 with hb1
    have b1r : -(C.p : Int) < b1 ∧ b1 < 2 * C.p := by rw [hb1]; split <;> omega
    rw [M₄] at e₅
    have A₅ := addIfNeg_step (wsucc _ _) (wv_lt _ _ _ _) (BitVec.isLt _) e₅ (by rw [A₄]; split <;> omega)
      (by rw [A₄]; split <;> omega)
    rw [A₄] at A₅
    set b2 := b1 + if b1 < 0 then (C.p : Int) else 0 with hb2
    have b2r : 0 ≤ b2 ∧ b2 < 2 * C.p := by rw [hb2]; split <;> omega
    -- `a mod p`.
    have A₅v : (wv s₅.mem C.B (slot C.w C.iX₂) (C.n + 1) : Int) = b2 := by
      unfold sgn at A₅
      split at A₅
      · exact A₅
      · have := wv_lt s₅.mem C.B (slot C.w C.iX₂) (C.n + 1)
        have : ((wv s₅.mem C.B (slot C.w C.iX₂) (C.n + 1) : Nat) : Int) < 2 ^ (64 * (C.n + 1)) := by
          exact_mod_cast this
        omega
    have hlt5 : wv s₅.mem C.B (slot C.w C.iX₂) (C.n + 1) < 2 * wv s₅.mem C.B (slot C.w C.iM) C.n := by
      rw [M₅]; have := b2r.2; rw [← A₅v] at this; exact_mod_cast this
    have e₆' := e₆ hlt5
    rw [M₅] at e₆'
    set r := wv s₅.mem C.B (slot C.w C.iX₂) (C.n + 1) % C.p with hr
    have rp : r < C.p := Nat.mod_lt _ (by omega)
    have r6 : wv s₆.mem C.B (slot C.w C.iX₂) C.n = r := by
      have h6 := wsucc s₆.mem C.iX₂
      rw [e₆'] at h6
      have := wv_lt s₆.mem C.B (slot C.w C.iX₂) C.n
      have : 2 ^ (64 * C.n) * (word s₆.mem C.B (slot C.w C.iX₂ + 8 * C.n)).toNat = 0 := by
        rcases Nat.eq_zero_or_pos (word s₆.mem C.B (slot C.w C.iX₂ + 8 * C.n)).toNat with h | h
        · rw [h, Nat.mul_zero]
        · have := Nat.mul_le_mul_left (2 ^ (64 * C.n)) h; omega
      omega
    -- The doublings.
    have r7 : wv s₇.mem C.B (slot C.w C.iX₂) C.n = r := by rw [m₇, r6]
    have x₂t : wv t.mem C.B (slot C.w C.iX₂) C.n = r * 2 ^ (15 * C.n + 10) % C.p := by
      rw [mt, hD.val (by rw [r7, M₇]; exact rp), r7, M₇]
    rw [x₂t, show 15 * C.n + 10 = 5 * (3 * C.n + 2) by omega]
    refine ⟨rr r ?_, Nat.mod_lt _ (by omega)⟩
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
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hk := Nat.div_add_mod (q * m) (2 ^ 64)
  rw [hqm] at hk
  set k := q * m / 2 ^ 64
  have e : ((q : Int) * ((2 ^ 64 - m : Nat) : Int) + 1) = 2 ^ 64 * ((q : Int) - k) := by
    have hk' : ((q : Int) * m) = 2 ^ 64 * k + 1 := by exact_mod_cast hk.symm
    rw [Nat.cast_sub (show m ≤ 2 ^ 64 by omega)]
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
  obtain ⟨mi, hmi⟩ := minv_exists (q := p + (1 - p % 2)) (by omega)
  let C : ICfg := ⟨B, Z, w, n, iU, iV, iX₁, iX₂, iM, iT, p, mi, Rsa.Divstep.oddInput p a⟩
  have hC : C.Ok := ⟨hn1, hnw, hw, hn21, hZ, hU, hV, hX₁, hX₂, hM, hT, dUV, dUX₁, dUX₂, dUM, dUT, dVX₁, dVX₂, dVM,
    dVT, dX, dX₁M, dX₁T, dX₂M, dX₂T, dMT, pC,
    by
      have := Rsa.Divstep.oddInput_lt (m := p) (x := a) pC aC
      show Rsa.Divstep.oddInput p a < 2 ^ (64 * n + 1)
      rw [Nat.pow_succ]; omega,
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
      Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  refine WP.ite (decide (w < 2 ^ 21)) (by
      show some (s₂.read .x .x3 == 0) = _
      congr 1
      have : s₂.read .x .x3 = s₂.gpr .x3 := rfl
      rw [this]
      by_cases hw21 : w < 2 ^ 21
      · rw [decide_eq_true hw21, beq_iff_eq]
        apply BitVec.eq_of_toNat_eq; rw [e3]; simp; omega
      · rw [decide_eq_false hw21]
        apply Bool.eq_false_iff.mpr
        intro hb
        rw [beq_iff_eq] at hb
        have := congrArg BitVec.toNat hb
        rw [e3] at this
        simp at this
        omega) (fun hb => ?_) (fun hb => ?_)
  · -- Batches of divsteps.
    have hw21 : w < 2 ^ 21 := by simpa using hb
    refine WP.mono (inverseB_ok hs₂ h0₂ ((k₂.gpr .x11 (by decide)).trans h11₁) ((k₂.gpr .x12 (by decide)).trans h12₁)
      (by omega) (Nat.le_refl _) hw hw21 h.hZ hU hV hX₁ hX₂ hM hT dUV dUX₁ dUX₂ dUM dUT dVX₁ dVX₂ dVM dVT dX dX₁M dX₁T
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
    · exact ⟨ar w iU, by simp, Nat.le_refl _, Nat.add_le_add_left (show 8 * w ≤ 8 * (w + 2) by omega) _⟩
    · exact ⟨ar w iV, by simp, Nat.le_refl _, Nat.add_le_add_left (show 8 * w ≤ 8 * (w + 2) by omega) _⟩
    · exact ⟨ar w iX₁, by simp, Nat.le_refl _, Nat.add_le_add_left (show 8 * w ≤ 8 * (w + 2) by omega) _⟩
    · exact ⟨ar w iX₂, by simp, Nat.le_refl _, Nat.add_le_add_left (show 8 * w ≤ 8 * (w + 2) by omega) _⟩
    · exact ⟨ar w iT, by simp, Nat.le_refl _, Nat.le_refl _⟩

end VG.Proof.Rsa.AArch64

-- From `Proof/Rsa/AArch64/Instances.lean`.
/-! # The proofs supplied at the RSA registrations on AArch64

The inverse's contract (`InvLaw`), proved in `InvFinish.lean`.
-/


namespace VG.Proof.Rsa.AArch64

instance invLaw : InvLaw where
  inverse_ok := inverse_ok

end VG.Proof.Rsa.AArch64
