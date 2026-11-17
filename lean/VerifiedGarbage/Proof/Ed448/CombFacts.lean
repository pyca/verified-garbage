module

public import VerifiedGarbage.Proof.Ed448.CombRef
import VerifiedGarbage.Proof.Ed448.Comb
import VerifiedGarbage.Proof.Ed448.Group.Projective
import VerifiedGarbage.Proof.Ed448.Group.Decode
import VerifiedGarbage.Proof.Ed448.VerifyEq
import VerifiedGarbage.Proof.Ed25519.SlidingDigits
import VerifiedGarbage.Proof.X448.BaseAdd
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Abel

/-!
# Ed448: the four-column comb agrees with the specification

Untrusted and target-independent, and heavy, as `Facts.lean`: the group law
over `ZMod p`. `baseComb_ok`: after the rows above `t`, `comb` represents
`[accScalar k t]B` (`comb_rep`, from the table's entries, `Comb.entry_rep`,
and the scalar's arithmetic, `Comb.accScalar_step`), so the whole comb
encodes `[k]B`; and `baseCombU_ok`, X448 of the base point as its
u-coordinate (`Proof/X448/BaseAdd.lean`). `verifyEqComb_ok`: `vcomb` represents
`[accScalar S t]B + [∑ j, 2^j D (t + j)]a` the same way, for `k`'s digits `D`
(the scalar of the comb is zero above its rows; a digit's multiple is the
table's, `oddMul_rep`; the digits sum to `k`, `Slide.digits_sum`), and the
equation follows (`verifyEquation_some`).

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

/-! ## X448 of the base point -/

theorem baseCombU_ok : BaseCombUOk := fun kb => by
  have hlt : Spec.X448.decodeScalar448 kb < 2 ^ 448 := by
    rw [Spec.X448.decodeScalar448, VG.Proof.X448.decodeLittleEndian_eq]
    refine Nat.lt_of_lt_of_le (VG.Proof.X25519.leNum_lt _) ?_
    rw [show (2 : Nat) ^ 448 = 256 ^ 56 by decide +kernel]
    exact Nat.pow_le_pow_right (by decide) (List.length_take_le _ _)
  refine ⟨fun t ht => ?_, ?_⟩
  · rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt
      (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) ht))]
    rfl
  · have h := comb_rep (Spec.X448.decodeScalar448 kb) 114 (Nat.le_refl _)
    rw [Nat.sub_self, Comb.accScalar_total _ (Nat.lt_of_lt_of_le hlt (by decide +kernel))] at h
    refine VG.Proof.X448.Edwards.x448_basePoint kb _ ?_
    rw [VG.Proof.X448.invert_eq]
    exact VG.Proof.X448.u_rep h

/-! ## Verification's equation -/

/-- Above its rows, the comb's scalar is zero. -/
private theorem accScalar_high (k : Nat) {n : Nat} (hn : 114 ≤ n) : accScalar k n = 0 := by
  have h (x : Nat) : x % 2 ^ 114 / 2 ^ n = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by decide) hn))
  simp only [accScalar, h, Nat.zero_mul, Nat.add_zero]

/-- A table's entry `m` represents `[2m + 1]a`. -/
private theorem oddMul_rep {a' : Point} {a : EPoint dZ} (ha : Rep a' a) :
    ∀ m, Rep (oddMul a' m) ((2 * m + 1) • a)
  | 0 => by simpa only [oddMul, Nat.mul_zero, Nat.zero_add, one_nsmul] using ha
  | m + 1 => by
    have h := pointAdd_rep (oddMul_rep ha m) (double_rep ha)
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by omega_arith, add_nsmul, add_nsmul, one_nsmul, add_assoc]
    exact h

/-- One bit: `Q` for `[accScalar S (t + 1)]B + [x]a` becomes `Q` for `[accScalar S t]B + [d + 2x]a`,
for the digit `d` at `t`, zero or odd. -/
private theorem vcombStep_rep {q a' : Point} {S d x t : Nat} {a : EPoint dZ}
    (hr : Rep q (accScalar S (t + 1) • baseAff + x • a)) (ha : Rep a' a) (hd : d = 0 ∨ d % 2 = 1) :
    Rep (vcombStep S d t a' q) (accScalar S t • baseAff + (d + 2 * x) • a) := by
  have h2 := double_rep hr
  have hk : (d + 2 * x) • a = x • a + x • a + d • a := by
    rw [add_nsmul, two_mul, add_nsmul]
    abel
  have hm := oddMul_rep ha ((d - 1) / 2)
  unfold vcombStep
  by_cases hrow : t < 114
  · have h3 := pointAdd_rep h2 (Comb.entry_rep _ (Comb.digit_lt S t))
    have e1 : accScalar S t • baseAff + (d + 2 * x) • a =
        (accScalar S (t + 1) • baseAff + x • a) + (accScalar S (t + 1) • baseAff + x • a) +
          Impl.Ed448.Comb.weight (digit S t) • baseAff + d • a := by
      rw [hk, Comb.accScalar_step S t hrow, add_nsmul, two_mul, add_nsmul]
      abel
    rw [e1]
    rcases hd with rfl | h1
    · simp only [hrow, combDigit_eq, zero_nsmul, add_zero, ite_true]
      exact h3
    · rw [show 2 * ((d - 1) / 2) + 1 = d by omega_using [h1]] at hm
      simp only [hrow, combDigit_eq, ite_true, show d ≠ 0 by omega_using [h1], ite_false]
      exact pointAdd_rep h3 hm
  · have e1 : accScalar S t • baseAff + (d + 2 * x) • a =
        (accScalar S (t + 1) • baseAff + x • a) + (accScalar S (t + 1) • baseAff + x • a) + d • a := by
      rw [hk, accScalar_high S (n := t) (by omega_using [hrow]), accScalar_high S (n := t + 1) (by omega_using [hrow]),
        zero_nsmul, zero_add, zero_add]
    rw [e1]
    rcases hd with rfl | h1
    · simp only [hrow, zero_nsmul, add_zero, ite_true, ite_false]
      exact h2
    · rw [show 2 * ((d - 1) / 2) + 1 = d by omega_using [h1]] at hm
      simp only [hrow, show d ≠ 0 by omega_using [h1], ite_false]
      exact pointAdd_rep h2 hm

private theorem vcomb_rep (S K : Nat) {a' : Point} {a : EPoint dZ} (ha : Rep a' a) :
    ∀ m ≤ 456, Rep (vcomb S K a' m)
      (accScalar S (456 - m) • baseAff + Proof.Ed25519.Slide.wsum (vdigits K) (456 - m) m • a)
  | 0, _ => by
    rw [Nat.sub_zero, accScalar_high S (by decide), Proof.Ed25519.Slide.wsum_zero, zero_nsmul, zero_nsmul, add_zero]
    exact identity_rep
  | m + 1, hm => by
    have h := vcombStep_rep (S := S) (t := 455 - m) (show Rep (vcomb S K a' m)
      (accScalar S (455 - m + 1) • baseAff + Proof.Ed25519.Slide.wsum (vdigits K) (455 - m + 1) m • a) by
      rw [show 455 - m + 1 = 456 - m by omega_arith]; exact vcomb_rep S K ha m (by omega_arith)) ha
      (d := vdigits K (455 - m))
      ((Proof.Ed25519.Slide.digits_odd 456 K (455 - m)).imp id fun h => h.1)
    rw [show 456 - (m + 1) = 455 - m by omega_arith, Proof.Ed25519.Slide.wsum_succ]
    exact h

theorem verifyEqComb_ok : VerifyEqCombOk := by
  intro pk sig ch a r hl hs hc ha hr
  have hva := decodePoint_valid ha
  have hS := decodeLE_below (bs := sig.drop 57) (by rw [List.length_drop, hs])
  have hQ := vcomb_rep (Spec.Ed448.decodeLE (sig.drop 57)) (Spec.Ed448.decodeLE ch)
    (rep_toAffine (valid_negPoint hva)) 456 (Nat.le_refl _)
  rw [Nat.sub_self, Proof.Ed25519.Slide.digits_sum (decodeLE_below hc), Comb.accScalar_total _ hS,
    toAffine_negPoint hva] at hQ
  exact verifyEquation_some hl hs hc ha hr hQ (rep_toAffine (decodePoint_valid hr))

end VG.Proof.Ed448
