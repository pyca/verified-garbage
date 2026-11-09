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

theorem bit_zero {k t : Nat} (hk : k < 2 ^ 456) (ht : 456 ≤ t) : k / 2 ^ t = 0 :=
  Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) ht))

def signedPoint (b : Bool) (p : Point) : Point := if b then negPoint p else p

theorem signedPoint_rep {p : Point} {a : EPoint dZ} {n : Nat} (h : Rep p (n • a)) (b : Bool) :
    Rep (signedPoint b p) ((if b then -(n : Int) else n) • a) := by
  cases b
  · simpa only [signedPoint, Bool.false_eq_true, ite_false, natCast_zsmul] using h
  · simpa only [signedPoint, ite_true, neg_zsmul, natCast_zsmul] using h.neg

end VG.Proof.Ed448.SignedWindow
