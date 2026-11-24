module

public import VerifiedGarbage.Proof.Ed448.SignedComb
import VerifiedGarbage.Proof.Ed448.Group.Projective
import VerifiedGarbage.Proof.Ed448.Group.Decode
import VerifiedGarbage.Proof.X448.BaseDigits
import VerifiedGarbage.Proof.X448.BaseAdd
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Ring

/-!
# edwards448: the signed radix-16 comb agrees with the specification

Untrusted and target-independent, and heavy, as `CombFacts.lean`: the group law
over `ZMod p`. An accumulator represents `[G + Σ d_j 256^j] B` (`signedSum_rep`,
from the tables' entries, `baseEntry_ok`), so the comb `[k] B`
(`signedComb_rep`, by `comb_total`).

Only registration files import this module.
-/

@[expose] public section

namespace VG.Proof.Ed448

set_option exponentiation.threshold 1024

open Spec.Ed448 (Point)
open EdwardsLaw
open VG.Proof.X448

private theorem affAdd_eq (p : Point) (q : Spec.X448.Fe × Spec.X448.Fe) :
    affAdd p q = addPt p (basePt q) := by
  simp only [affAdd, addPt, basePt, Point.mk.injEq]
  refine ⟨Ed448.toZ_inj.1 ?_, Ed448.toZ_inj.1 ?_, Ed448.toZ_inj.1 ?_⟩ <;>
    simp only [toZ_add, toZ_sub, toZ_mul, toZ_zero, toZ_one] <;> ring

/-- The sum of the digits of parity `o` below table `c`. -/
private def sumZ (k o : Nat) : Nat → ℤ
  | 0 => 0
  | c + 1 => sumZ k o c + sdig k (2 * c + o) * 256 ^ c

private theorem signedSum_rep (k o : Nat) : ∀ c ≤ 57,
    Rep (signedSum k o c) (((combG 57 : ℤ) + sumZ k o c) • baseAff)
  | 0, _ => by
    have h := baseG57_ok
    rw [← combG_57] at h
    simp only [signedSum, sumZ, add_zero, natCast_zsmul]
    exact h
  | c + 1, hc => by
    have h := addPt_rep (signedSum_rep k o c (by omega_using [hc])) (baseEntry_ok c (nib k (2 * c + o)) (by omega_using [hc]) (nib_lt _ _))
    rw [← affAdd_eq] at h
    simp only [signedSum, sumZ, sdig]
    rw [← add_assoc, add_smul _ _ baseAff]
    exact h

private theorem sumZ_odd (k : Nat) : ∀ c, sumZ k 1 c = oddSumZ k c
  | 0 => rfl
  | c + 1 => by rw [sumZ, oddSumZ, sumZ_odd k c]

private theorem sumZ_even (k : Nat) : ∀ c, sumZ k 0 c = evenSumZ k c
  | 0 => rfl
  | c + 1 => by rw [sumZ, evenSumZ, sumZ_even k c]; rfl

private theorem signedComb_rep {k : Nat} (hk : k < 256 ^ 57) : Rep (signedComb k) (k • baseAff) := by
  have ho := signedSum_rep k 1 57 (Nat.le_refl _)
  have he := signedSum_rep k 0 57 (Nat.le_refl _)
  have h := pointAdd_rep (double_rep (double_rep (double_rep (double_rep ho)))) he
  have e : (k : ℕ) • baseAff = ((k : ℤ)) • baseAff := (natCast_zsmul _ _).symm
  rw [e, ← comb_total hk, ← sumZ_odd, ← sumZ_even]
  generalize (combG 57 : ℤ) + sumZ k 1 57 = x at *
  generalize (combG 57 : ℤ) + sumZ k 0 57 = y at *
  rw [signedComb]
  have e2 : (16 * x + y) • baseAff = x • baseAff + x • baseAff + (x • baseAff + x • baseAff) +
      (x • baseAff + x • baseAff + (x • baseAff + x • baseAff)) +
      (x • baseAff + x • baseAff + (x • baseAff + x • baseAff) +
      (x • baseAff + x • baseAff + (x • baseAff + x • baseAff))) + y • baseAff := by
    simp only [← add_smul]
    congr 1
    ring
  rw [e2]
  exact h

theorem signedBase_ok : SignedBaseOk := fun k hk => by
  have h := signedComb_rep (k := k) (Nat.lt_of_lt_of_le hk (by decide +kernel))
  rw [encodePoint_rep h, encodePoint_rep (pointMul_rep k basePoint_rep)]

theorem signedBaseU_ok : SignedBaseUOk := fun kb => by
  have hlt : Spec.X448.decodeScalar448 kb < 2 ^ 448 := by
    rw [Spec.X448.decodeScalar448, VG.Proof.X448.decodeLittleEndian_eq]
    refine Nat.lt_of_lt_of_le (VG.Proof.X25519.leNum_lt _) ?_
    rw [show (2 : Nat) ^ 448 = 256 ^ 56 by decide +kernel]
    exact Nat.pow_le_pow_right (by decide) (List.length_take_le _ _)
  refine ⟨fun t ht => ?_, ?_⟩
  · rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt
      (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) ht))]
    rfl
  · refine VG.Proof.X448.Edwards.x448_basePoint kb _ ?_
    rw [VG.Proof.X448.invert_eq]
    exact VG.Proof.X448.u_rep (signedComb_rep (Nat.lt_of_lt_of_le hlt (by decide +kernel)))

end VG.Proof.Ed448
