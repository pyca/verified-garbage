module

public import VerifiedGarbage.Proof.Ed448.CombRef
import VerifiedGarbage.Proof.Ed448.Comb
import VerifiedGarbage.Proof.Ed448.Group.Projective
import VerifiedGarbage.Proof.Ed448.Group.Decode
import VerifiedGarbage.Proof.Ed448.VerifyEq
import VerifiedGarbage.Proof.Ed448.Facts
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Abel

/-!
# Ed448: the four-column comb agrees with the specification

Untrusted and target-independent, and heavy, as `Facts.lean`: the group law
over `ZMod p`. `baseComb_ok`: after the rows above `t`, `comb` represents
`[accScalar k t]B` (`comb_rep`, from the table's entries, `Comb.entry_rep`,
and the scalar's arithmetic, `Comb.accScalar_step`), so the whole comb
encodes `[k]B`. `verifyEqComb_ok`: `vcomb` represents
`[accScalar S t]B + [k >> t]a` the same way (the scalar of the comb is zero
above its rows), and the equation follows (`verifyEquation_some`).

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

/-! ## Verification's equation -/

/-- Above its rows, the comb's scalar is zero. -/
private theorem accScalar_high (k : Nat) {n : Nat} (hn : 114 ≤ n) : accScalar k n = 0 := by
  have h (x : Nat) : x % 2 ^ 114 / 2 ^ n = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by decide) hn))
  simp only [accScalar, h, Nat.zero_mul, Nat.add_zero]

/-- One bit: `Q` for `[accScalar S (t + 1)]B + [k >> (t + 1)]a` becomes `Q` for
`[accScalar S t]B + [k >> t]a`. -/
private theorem vcombStep_rep {q a' : Point} {S K t : Nat} {a : EPoint dZ}
    (hr : Rep q (accScalar S (t + 1) • baseAff + (K >>> (t + 1)) • a)) (ha : Rep a' a) :
    Rep (vcombStep S (bitAt K t) t a' q) (accScalar S t • baseAff + (K >>> t) • a) := by
  have h2 := double_rep hr
  have hk : (K >>> t) • a = (K >>> (t + 1)) • a + (K >>> (t + 1)) • a + ((K >>> t) &&& 1) • a := by
    conv => lhs; rw [shift_step K t]
    rw [add_nsmul, two_mul, add_nsmul]
  unfold vcombStep
  by_cases hrow : t < 114
  · have h3 := pointAdd_rep h2 (Comb.entry_rep _ (Comb.digit_lt S t))
    have e1 : accScalar S t • baseAff + (K >>> t) • a =
        (accScalar S (t + 1) • baseAff + (K >>> (t + 1)) • a) +
          (accScalar S (t + 1) • baseAff + (K >>> (t + 1)) • a) +
          Impl.Ed448.Comb.weight (digit S t) • baseAff + ((K >>> t) &&& 1) • a := by
      rw [hk, Comb.accScalar_step S t hrow, add_nsmul, two_mul, add_nsmul]
      abel
    rw [e1]
    rcases bit_cases K t with ⟨hb, bk⟩ | ⟨hb, bk⟩ <;>
      simp only [hrow, hb, bk, combDigit_eq, zero_nsmul, add_zero, one_nsmul, Bool.false_eq_true, ite_true,
        ite_false]
    · exact h3
    · exact pointAdd_rep h3 ha
  · have e1 : accScalar S t • baseAff + (K >>> t) • a =
        (accScalar S (t + 1) • baseAff + (K >>> (t + 1)) • a) +
          (accScalar S (t + 1) • baseAff + (K >>> (t + 1)) • a) + ((K >>> t) &&& 1) • a := by
      rw [hk, accScalar_high S (n := t) (by omega_using [hrow]), accScalar_high S (n := t + 1) (by omega_using [hrow]),
        zero_nsmul, zero_add, zero_add]
    rw [e1]
    rcases bit_cases K t with ⟨hb, bk⟩ | ⟨hb, bk⟩ <;>
      simp only [hrow, hb, bk, zero_nsmul, add_zero, one_nsmul, Bool.false_eq_true, ite_true, ite_false]
    · exact h2
    · exact pointAdd_rep h2 ha

private theorem vcomb_rep {S K : Nat} (hK : Below456 K) {a' : Point} {a : EPoint dZ} (ha : Rep a' a) :
    ∀ m ≤ 456, Rep (vcomb S K a' m) (accScalar S (456 - m) • baseAff + (K >>> (456 - m)) • a)
  | 0, _ => by
    rw [Nat.sub_zero, accScalar_high S (by decide), shift_456 hK, zero_nsmul, zero_nsmul, add_zero]
    exact identity_rep
  | m + 1, hm => by
    have h := vcombStep_rep (S := S) (t := 455 - m) (show Rep (vcomb S K a' m)
      (accScalar S (455 - m + 1) • baseAff + (K >>> (455 - m + 1)) • a) by
      rw [show 455 - m + 1 = 456 - m by omega_arith]; exact vcomb_rep hK ha m (by omega_arith)) ha
    rw [show 456 - (m + 1) = 455 - m by omega_arith]
    exact h

theorem verifyEqComb_ok : VerifyEqCombOk := by
  intro pk sig ch a r hl hs hc ha hr
  have hva := decodePoint_valid ha
  have hS := decodeLE_below (bs := sig.drop 57) (by rw [List.length_drop, hs])
  have hQ := vcomb_rep (S := Spec.Ed448.decodeLE (sig.drop 57)) (decodeLE_below hc)
    (rep_toAffine (valid_negPoint hva)) 456 (Nat.le_refl _)
  rw [Nat.sub_self, Nat.shiftRight_zero, Comb.accScalar_total _ hS, toAffine_negPoint hva] at hQ
  exact verifyEquation_some hl hs hc ha hr hQ (rep_toAffine (decodePoint_valid hr))

end VG.Proof.Ed448
