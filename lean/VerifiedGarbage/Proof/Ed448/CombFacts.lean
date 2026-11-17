module

public import VerifiedGarbage.Proof.Ed448.CombRef
import VerifiedGarbage.Proof.Ed448.Comb
import VerifiedGarbage.Proof.Ed448.Group.Projective
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Ed448: the four-column comb agrees with the specification

Untrusted and target-independent, and heavy, as `Facts.lean`: the group law
over `ZMod p`. `baseComb_ok`: after the rows above `t`, `comb` represents
`[accScalar k t]B` (`comb_rep`, from the table's entries, `Comb.entry_rep`,
and the scalar's arithmetic, `Comb.accScalar_step`), so the whole comb
encodes `[k]B`.

Only registration files import this module.
-/

@[expose] public section

namespace VG.Proof.Ed448

set_option exponentiation.threshold 1024

open Spec.Ed448 (Point)
open EdwardsLaw
open VG.Proof.Ed448.Comb (digit accScalar)

private theorem combDigit_eq (k t : Nat) : combDigit k t = digit k t := by
  simp only [combDigit, digit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  omega_arith

/-- One row: `R` for `[accScalar k (t + 1)]B` becomes `R` for `[accScalar k t]B`. -/
private theorem combRow_rep {r : Point} {k t : Nat} (ht : t < 114) (hr : Rep r (accScalar k (t + 1) • baseAff)) :
    Rep (combRow k t r) (accScalar k t • baseAff) := by
  have h := pointAdd_rep (double_rep hr) (Comb.entry_rep _ (Comb.digit_lt k t))
  rw [← two_nsmul, smul_smul, ← add_nsmul, ← Comb.accScalar_step k t ht] at h
  rw [combRow, combDigit_eq]
  exact h

private theorem comb_rep (k : Nat) : ∀ m ≤ 114, Rep (comb k m) (accScalar k (114 - m) • baseAff)
  | 0, _ => by rw [Nat.sub_zero, Comb.accScalar_start, zero_nsmul]; exact identity_rep
  | m + 1, hm => by
    have h := combRow_rep (k := k) (t := 113 - m) (by omega_arith)
      (show Rep (comb k m) (accScalar k (113 - m + 1) • baseAff) by
        rw [show 113 - m + 1 = 114 - m by omega_arith]; exact comb_rep k m (by omega_arith))
    rw [show 114 - (m + 1) = 113 - m by omega_arith]
    exact h

theorem baseComb_ok : BaseCombOk := fun k hk => by
  have h := comb_rep k 114 (Nat.le_refl _)
  rw [Nat.sub_self, Comb.accScalar_total k hk] at h
  rw [encodePoint_rep h, encodePoint_rep (pointMul_rep k basePoint_rep)]

end VG.Proof.Ed448
