module

public import VerifiedGarbage.Proof.Ed448.WinRef
import VerifiedGarbage.Proof.Ed448.CombFacts
import VerifiedGarbage.Proof.Ed448.SignedCombFacts
import VerifiedGarbage.Proof.Ed448.WnafWide.Group
import VerifiedGarbage.Proof.Ed448.Group.Projective
import VerifiedGarbage.Proof.Ed448.Group.Decode
import VerifiedGarbage.Proof.Ed448.VerifyEq
import VerifiedGarbage.Proof.Ed25519.SlidingDigits
import VerifiedGarbage.Proof.X448.BaseAdd
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Abel

-- separate module: heavy (the group law), imported by the registration files' proofs alone

/-!
# Ed448: verification's two sliding windows agree with the specification

Untrusted and target-independent, and heavy, as `CombFacts.lean`: `vwin`
represents `[∑ j, 2^j E (t + j)]B + [∑ j, 2^j D (t + j)]a`, for `S`'s digits
`E` and `k`'s `D` (`vwin_rep`: a digit's multiple is the table's,
`publicTable_rep` and `oddMul_rep`), whose sums are `S` and `k`
(`Slide.digitsW_sum`), and the equation follows (`verifyEquation_some`).

Only registration files' proofs import this module.
-/

@[expose] public section

namespace VG.Proof.Ed448

open Spec.Ed448 (Point)
open EdwardsLaw
open VG.Proof.X448 (basePt addPt_rep)
open Proof.Ed25519 (Slide.wsum Slide.wsum_succ Slide.wsum_zero)

/-- One bit: `Q` for `[y]B + [x]a` becomes `Q` for `[e + 2y]B + [d + 2x]a`, for the digits `e` and
`d`, each zero or odd, `e` below 128. -/
private theorem vwinStep_rep {q a' : Point} {e d x y : Nat} {a : EPoint dZ}
    (hr : Rep q (y • baseAff + x • a)) (ha : Rep a' a) (he : e = 0 ∨ (e % 2 = 1 ∧ e < 2 ^ 7))
    (hd : d = 0 ∨ d % 2 = 1) :
    Rep (vwinStep e d a' q) ((e + 2 * y) • baseAff + (d + 2 * x) • a) := by
  have h2 := double_rep hr
  have h3 : Rep (if e = 0 then double q else affAdd (double q) (Impl.Ed448.PublicTable.entry ((e - 1) / 2)))
      ((y • baseAff + x • a) + (y • baseAff + x • a) + e • baseAff) := by
    rcases he with rfl | ⟨h1, hlt⟩
    · simpa only [zero_nsmul, add_zero, ite_true] using h2
    · have ht := WnafWide.publicTable_rep ((e - 1) / 2) (by omega_using [hlt, h1])
      rw [show 2 * ((e - 1) / 2) + 1 = e by omega_using [h1]] at ht
      simp only [show e ≠ 0 by omega_using [h1], ite_false]
      rw [affAdd_eq]
      exact addPt_rep h2 ht
  have e1 : (e + 2 * y) • baseAff + (d + 2 * x) • a =
      (y • baseAff + x • a) + (y • baseAff + x • a) + e • baseAff + d • a := by
    rw [add_nsmul, add_nsmul, two_mul, two_mul, add_nsmul, add_nsmul]
    abel
  rw [e1]
  unfold vwinStep
  rcases hd with rfl | h1
  · simpa only [zero_nsmul, add_zero, ite_true] using h3
  · have hm := oddMul_rep ha ((d - 1) / 2)
    rw [show 2 * ((d - 1) / 2) + 1 = d by omega_using [h1]] at hm
    simp only [show d ≠ 0 by omega_using [h1], ite_false]
    exact pointAdd_rep h3 hm

private theorem vwin_rep (S K : Nat) {a' : Point} {a : EPoint dZ} (ha : Rep a' a) :
    ∀ m ≤ 456, Rep (vwin S K a' m)
      (Slide.wsum (bdigits S) (456 - m) m • baseAff + Slide.wsum (vdigits K) (456 - m) m • a)
  | 0, _ => by
    rw [Slide.wsum_zero, Slide.wsum_zero, zero_nsmul, zero_nsmul, add_zero]
    exact identity_rep
  | m + 1, hm => by
    have h := vwinStep_rep (show Rep (vwin S K a' m)
      (Slide.wsum (bdigits S) (455 - m + 1) m • baseAff + Slide.wsum (vdigits K) (455 - m + 1) m • a) by
      rw [show 455 - m + 1 = 456 - m by omega_arith]; exact vwin_rep S K ha m (by omega_arith)) ha
      (e := bdigits S (455 - m)) (d := vdigits K (455 - m))
      (Proof.Ed25519.Slide.digitsW_odd (by decide) 456 S (455 - m))
      ((Proof.Ed25519.Slide.digits_odd 456 K (455 - m)).imp id fun h => h.1)
    rw [show 456 - (m + 1) = 455 - m by omega_arith, Slide.wsum_succ, Slide.wsum_succ]
    exact h

theorem verifyEqWin_ok : VerifyEqWinOk := by
  intro pk sig ch a r hl hs hc ha hr
  have hva := decodePoint_valid ha
  have hS := decodeLE_below (bs := sig.drop 57) (by rw [List.length_drop, hs])
  have hQ := vwin_rep (Spec.Ed448.decodeLE (sig.drop 57)) (Spec.Ed448.decodeLE ch)
    (rep_toAffine (valid_negPoint hva)) 456 (Nat.le_refl _)
  rw [Nat.sub_self, Proof.Ed25519.Slide.digits_sum (decodeLE_below hc),
    Proof.Ed25519.Slide.digitsW_sum (by decide) hS, toAffine_negPoint hva] at hQ
  exact verifyEquation_some hl hs hc ha hr hQ (rep_toAffine (decodePoint_valid hr))

end VG.Proof.Ed448
