module

public import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Add
public import VerifiedGarbage.Impl.Ed448.Wnaf
import VerifiedGarbage.Proof.Ed448.Wnaf.Recoding
import Mathlib.Tactic.Abel
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig

/-! The sparse loop's group interpretation. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Wnaf
open VG.Proof.Ed448 VG.Proof.EdwardsLaw
open VG.Impl.Ed448.Wnaf (residual digitAt)

theorem signed_abs (d : Int) : (if decide (d < 0) then -(d.natAbs : Int) else (d.natAbs : Int)) = d := by
  by_cases hd : d < 0 <;> simp only [hd, decide_true, decide_false, ite_true, Bool.false_eq_true, ite_false] <;> omega

theorem baseEntry_rep {d : Int} (hd : -15 ≤ d ∧ d ≤ 15) :
    Rep (Proof.X448.basePt (baseEntry d)) (d • baseAff) := by
  have h := SignedWindow.signedPoint_rep (SignedWindow.entry_rep d.natAbs (abs_lt hd)) (decide (d < 0))
  rw [signed_abs] at h
  have he : Proof.X448.basePt (baseEntry d) = SignedWindow.signedPoint (decide (d < 0))
      (Proof.X448.basePt (Impl.Ed448.SignedWindow.entry d.natAbs)) := by
    by_cases hn : d < 0 <;>
      simp only [baseEntry, Proof.X448.basePt, hn, decide_true, decide_false, SignedWindow.signedPoint,
        ite_true, Bool.false_eq_true, ite_false, negPoint, zero_sub]
  rw [he]; exact h

theorem maybeAdd_rep {p q : Spec.Ed448.Point} {a b : EPoint dZ} {d : Int}
    (hp : Rep p a) (hq : Rep q (d • b)) : Rep (maybeAdd d p q) (a + d • b) := by
  by_cases hd : d = 0
  · simpa only [maybeAdd, hd, ite_true, zero_smul, add_zero] using hp
  · rw [maybeAdd, ite_eq_right hd]
    exact pointAdd_rep hp hq

theorem round_rep {p q : Spec.Ed448.Point} {a : EPoint dZ} {S K n : Nat}
    (hp : Rep p ((residual S (n + 1) : Int) • baseAff + (residual K (n + 1) : Int) • a))
    (hq : Rep q ((digitAt K n) • a)) :
    Rep (maybeAdd (digitAt K n)
      (maybeAdd (digitAt S n) (double p) (Proof.X448.basePt (baseEntry (digitAt S n)))) q)
      ((residual S n : Int) • baseAff + (residual K n : Int) • a) := by
  have h := maybeAdd_rep (maybeAdd_rep (double_rep hp)
    (baseEntry_rep (Proof.Ed448.Wnaf.digit_bounds (residual S n)))) hq
  convert h using 1
  · rfl
  · rw [Proof.Ed448.Wnaf.residual_step S n, Proof.Ed448.Wnaf.residual_step K n, add_zsmul,
      add_zsmul, mul_smul, mul_smul, two_zsmul, two_zsmul]
    simp only [digitAt]
    abel

end VG.Proof.Ed448.X86_64.Wnaf
