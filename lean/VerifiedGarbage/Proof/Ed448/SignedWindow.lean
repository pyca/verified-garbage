module

public import VerifiedGarbage.Impl.Ed448.SignedWindow
public import VerifiedGarbage.Proof.X448.BaseTable
import VerifiedGarbage.Proof.Ed448.Window
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import VerifiedGarbage.Proof.Framework.Omega

/-! Balanced five-bit recoding, including all 456 input bits. -/

@[expose] public section

namespace VG.Proof.Ed448.SignedWindow
set_option exponentiation.threshold 1024

open VG.Spec.Ed448 VG.Proof.Ed448 VG.Proof.EdwardsLaw

private theorem entry16_check :
    let p := pointMul 16 basePoint
    let q := Impl.Ed448.SignedWindow.entry 16
    q.1 * p.Z = p.X ∧ q.2 * p.Z = p.Y := by decide +kernel

theorem entry_rep (i : Nat) (hi : i < 17) :
    Rep (VG.Proof.X448.basePt (Impl.Ed448.SignedWindow.entry i)) (i • baseAff) := by
  by_cases he : i = 16
  · subst i
    exact VG.Proof.X448.basePt_rep (pointMul_rep _ basePoint_rep) entry16_check.1 entry16_check.2
  · simpa only [Impl.Ed448.SignedWindow.entry, ite_eq_right he] using Window.entry_rep i (by omega)

def carry (k t : Nat) : Nat := if t = 0 then 0 else k / 2 ^ (t - 1) % 2

def negative (k t : Nat) : Bool := decide (k / 2 ^ (t + 4) % 2 = 1)

def low (k t : Nat) : Nat := k / 2 ^ t % 16 + carry k t

def magnitude (k t : Nat) : Nat := if negative k t then 16 - low k t else low k t

def digit (k t : Nat) : Int := if negative k t then -(magnitude k t : Int) else magnitude k t

def high (k n : Nat) : Nat := k / 2 ^ (5 * n) + carry k (5 * n)

theorem carry_lt (k t : Nat) : carry k t < 2 := by unfold carry; split <;> omega

theorem low_le (k t : Nat) : low k t ≤ 16 := by have := carry_lt k t; unfold low; omega

theorem magnitude_lt (k t : Nat) : magnitude k t < 17 := by
  have := low_le k t; unfold magnitude; split <;> omega

theorem digit_eq (k t : Nat) :
    digit k t = ((k / 2 ^ t % 32 : Nat) : Int) + carry k t - 32 * ((k / 2 ^ (t + 4) % 2 : Nat) : Int) := by
  have he : k / 2 ^ t % 32 = k / 2 ^ t % 16 + 16 * (k / 2 ^ (t + 4) % 2) := by
    simp only [Nat.pow_add, ← Nat.div_div_eq_div_mul]
    omega
  have hbit : k / 2 ^ (t + 4) % 2 < 2 := Nat.mod_lt _ (by decide)
  have hl := low_le k t
  unfold digit magnitude negative low at *
  by_cases h : k / 2 ^ (t + 4) % 2 = 1 <;> simp only [h, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false] <;> omega

theorem high_step (k n : Nat) :
    (high k n : Int) = 32 * (high k (n + 1) : Int) + digit k (5 * n) := by
  rw [digit_eq]
  have hc : carry k (5 * (n + 1)) = k / 2 ^ (5 * n + 4) % 2 := by
    simp only [carry, show ¬5 * (n + 1) = 0 by omega, ite_false,
      show 5 * (n + 1) - 1 = 5 * n + 4 by omega]
  have he : k / 2 ^ (5 * n) = 32 * (k / 2 ^ (5 * (n + 1))) + k / 2 ^ (5 * n) % 32 := by
    rw [show 5 * (n + 1) = 5 * n + 5 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    omega
  unfold high
  rw [hc]
  omega

theorem high_zero (k : Nat) : high k 0 = k := by simp [high, carry]

theorem bit_zero {k t : Nat} (hk : k < 2 ^ 456) (ht : 456 ≤ t) : k / 2 ^ t = 0 :=
  Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) ht))

theorem high_end {k : Nat} (hk : k < 2 ^ 456) : high k 92 = 0 := by
  simp only [high, carry, Nat.reduceMul, Nat.reduceEqDiff, ite_false, Nat.reduceSub,
    bit_zero hk (by decide : 456 ≤ 460), bit_zero hk (by decide : 456 ≤ 459), Nat.zero_mod, Nat.zero_add]

def signedPoint (b : Bool) (p : Point) : Point := if b then negPoint p else p

theorem signedPoint_rep {p : Point} {a : EPoint dZ} {n : Nat} (h : Rep p (n • a)) (b : Bool) :
    Rep (signedPoint b p) ((if b then -(n : Int) else n) • a) := by
  cases b
  · simpa only [signedPoint, Bool.false_eq_true, ite_false, natCast_zsmul] using h
  · simpa only [signedPoint, ite_true, neg_zsmul, natCast_zsmul] using h.neg

def signedEntry (k t : Nat) : Spec.X448.Fe × Spec.X448.Fe :=
  let q := Impl.Ed448.SignedWindow.entry (magnitude k t)
  (if negative k t then -q.1 else q.1, q.2)

theorem signedEntry_point (k t : Nat) :
    VG.Proof.X448.basePt (signedEntry k t) = signedPoint (negative k t)
      (VG.Proof.X448.basePt (Impl.Ed448.SignedWindow.entry (magnitude k t))) := by
  unfold signedEntry signedPoint
  split <;> rfl

theorem signedEntry_rep (k t : Nat) :
    Rep (VG.Proof.X448.basePt (signedEntry k t)) ((digit k t) • baseAff) := by
  rw [signedEntry_point]
  exact signedPoint_rep (entry_rep _ (magnitude_lt k t)) (negative k t)

end VG.Proof.Ed448.SignedWindow
