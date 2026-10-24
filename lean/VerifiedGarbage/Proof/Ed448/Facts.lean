module

import VerifiedGarbage.Proof.Ed448.VerifyEq
public import VerifiedGarbage.Proof.Ed448.Group.Projective
import VerifiedGarbage.Proof.Ed448.Group.Decode
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Ed448: the reference computations agree with the specification

Untrusted and target-independent, and heavy: the group law over `ZMod p`.
The facts `Ref.lean` states, which every target's proofs take as hypotheses:

* `recover_ok`: `recoverX` is `recoverRef` (ring identities);
* `baseLadder_ok`: after the top `m` bits of `k`, `ladder` represents
  `[k >> (456 - m)]B` (`ladder_rep`), so the whole ladder encodes `[k]B`;
* `verifyEq_ok`: `vladder` represents `[S >> n]B + [k >> n]a` the same way,
  and the equation follows (`verifyEquation_some`).

Only registration files, and the modules that pass its facts to them
(`X86/ScalarBaseOk.lean`, `X86/VerifyEquationOk.lean`), import this module.
-/

@[expose] public section

namespace VG.Proof.Ed448

open Spec.X448 (Fe P)
open Spec.Ed448 (Point)
open EdwardsLaw

/-! ## Recovering `x` -/

theorem recoverX_eq (y : Fe) (sign : Bool) :
    Spec.Ed448.recoverX y sign =
      let u := y * y - 1
      let v := Spec.Ed448.d * (y * y) - 1
      let t := u * u * u * v
      let x := t * rootPow (t * ((u * v) * (u * v)))
      if v * (x * x) ≠ u then none
      else if x = 0 && sign then none
      else some (if (x.val % 2 == 1) == sign then x else (x - x) - x) := by
  have e1 : Spec.Ed448.d * y * y = Spec.Ed448.d * (y * y) :=
    toZ_inj.mp (by simp only [toZ_mul]; ring)
  have e2 (u v : Fe) : u * u * u * u * u * v * v * v = u * u * u * v * ((u * v) * (u * v)) :=
    toZ_inj.mp (by simp only [toZ_mul]; ring)
  have e3 (v x : Fe) : v * x * x = v * (x * x) := toZ_inj.mp (by simp only [toZ_mul]; ring)
  have e4 (x : Fe) : 0 - x = (x - x) - x := toZ_inj.mp (by simp only [toZ_sub, toZ_zero]; ring)
  unfold Spec.Ed448.recoverX
  dsimp only
  rw [e1]
  generalize y * y - 1 = u
  generalize Spec.Ed448.d * (y * y) - 1 = v
  rw [e2 u v, ← rootPow_eq]
  generalize u * u * u * v * rootPow (u * u * u * v * (u * v * (u * v))) = x
  rw [e3 v x, e4 x]

theorem recover_ok : RecoverOk := fun y sign => by rw [recoverX_eq]; rfl

/-! ## The ladders -/

theorem shift_step (k t : Nat) : k >>> t = 2 * (k >>> (t + 1)) + ((k >>> t) &&& 1) := by
  rw [Nat.shiftRight_succ, Nat.and_one_is_mod]
  omega

theorem bit_cases (k t : Nat) : ((k >>> t) &&& 1 = 0 ∧ bitAt k t = false) ∨
    ((k >>> t) &&& 1 = 1 ∧ bitAt k t = true) := by
  have hb : (k >>> t) &&& 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  rcases (by omega : (k >>> t) &&& 1 = 0 ∨ (k >>> t) &&& 1 = 1) with h | h
  · exact .inl ⟨h, by simp [bitAt, h]⟩
  · exact .inr ⟨h, by simp [bitAt, h]⟩

/-- One bit: `R` for `[k >> (t + 1)]B` becomes `R` for `[k >> t]B`. -/
theorem ladderStep_rep {r : Point} {k t : Nat} (hr : Rep r ((k >>> (t + 1)) • baseAff)) :
    Rep (ladderStep (bitAt k t) r) ((k >>> t) • baseAff) := by
  have h2 := double_rep hr
  have e1 : (k >>> t) • baseAff = (k >>> (t + 1)) • baseAff + (k >>> (t + 1)) • baseAff +
      ((k >>> t) &&& 1) • baseAff := by
    conv => lhs; rw [shift_step k t]
    rw [add_nsmul, two_mul, add_nsmul]
  rw [e1]
  rcases bit_cases k t with ⟨h, hb⟩ | ⟨h, hb⟩
  · rw [h, zero_nsmul, add_zero, hb]; exact h2
  · rw [h, one_nsmul, hb]; exact pointAdd_rep h2 basePoint_rep

theorem ladder_rep {k : Nat} (hk : Below456 k) :
    ∀ m ≤ 456, Rep (ladder k m) ((k >>> (456 - m)) • baseAff)
  | 0, _ => by rw [Nat.sub_zero, shift_456 hk, zero_nsmul]; exact identity_rep
  | m + 1, hm => by
    have h := ladderStep_rep (t := 455 - m) (show Rep (ladder k m) ((k >>> (455 - m + 1)) • baseAff) by
      rw [show 455 - m + 1 = 456 - m by omega]; exact ladder_rep hk m (by omega))
    rw [show 456 - (m + 1) = 455 - m by omega]
    exact h

theorem baseLadder_ok : BaseLadderOk := fun k hk => by
  have h := ladder_rep hk 456 (Nat.le_refl _)
  rw [Nat.sub_self, Nat.shiftRight_zero] at h
  rw [encodePoint_rep h, encodePoint_rep (pointMul_rep k basePoint_rep)]

/-- `ladderStep_rep`, for `ladderStep2`. -/
theorem ladderStep2_rep {r : Point} {k t : Nat} (hr : Rep r ((k >>> (t + 1)) • baseAff)) :
    Rep (ladderStep2 (bitAt k t) r) ((k >>> t) • baseAff) := by
  have h2 := pointAdd_rep hr hr
  have e1 : (k >>> t) • baseAff = (k >>> (t + 1)) • baseAff + (k >>> (t + 1)) • baseAff +
      ((k >>> t) &&& 1) • baseAff := by
    conv => lhs; rw [shift_step k t]
    rw [add_nsmul, two_mul, add_nsmul]
  rw [e1]
  unfold ladderStep2
  rcases bit_cases k t with ⟨h, hb⟩ | ⟨h, hb⟩
  · rw [h, zero_nsmul, add_zero, hb]; exact h2
  · rw [h, one_nsmul, hb]; exact pointAdd_rep h2 basePoint_rep

theorem ladder2_rep {k : Nat} (hk : Below456 k) :
    ∀ m ≤ 456, Rep (ladder2 k m) ((k >>> (456 - m)) • baseAff)
  | 0, _ => by rw [Nat.sub_zero, shift_456 hk, zero_nsmul]; exact identity_rep
  | m + 1, hm => by
    have h := ladderStep2_rep (t := 455 - m) (show Rep (ladder2 k m) ((k >>> (455 - m + 1)) • baseAff) by
      rw [show 455 - m + 1 = 456 - m by omega]; exact ladder2_rep hk m (by omega))
    rw [show 456 - (m + 1) = 455 - m by omega]
    exact h

theorem baseLadder2_ok : BaseLadder2Ok := fun k hk => by
  have h := ladder2_rep hk 456 (Nat.le_refl _)
  rw [Nat.sub_self, Nat.shiftRight_zero] at h
  rw [encodePoint_rep h, encodePoint_rep (pointMul_rep k basePoint_rep)]

/-- One bit of both scalars: `Q` for `[S >> (t+1)]B + [k >> (t+1)]a` becomes `Q` for
`[S >> t]B + [k >> t]a`. -/
theorem vstepRef_rep {q a' : Point} {S K t : Nat} {a : EPoint dZ}
    (hr : Rep q ((S >>> (t + 1)) • baseAff + (K >>> (t + 1)) • a)) (ha : Rep a' a) :
    Rep (vstepRef (bitAt S t) (bitAt K t) a' q) ((S >>> t) • baseAff + (K >>> t) • a) := by
  have h2 := double_rep hr
  have e1 : (S >>> t) • baseAff + (K >>> t) • a =
      ((S >>> (t + 1)) • baseAff + (K >>> (t + 1)) • a) + ((S >>> (t + 1)) • baseAff + (K >>> (t + 1)) • a) +
        ((S >>> t) &&& 1) • baseAff + ((K >>> t) &&& 1) • a := by
    conv => lhs; rw [shift_step S t, shift_step K t]
    rw [add_nsmul, add_nsmul, two_mul, two_mul, add_nsmul, add_nsmul]
    abel
  rw [e1]
  unfold vstepRef
  rcases bit_cases S t with ⟨hs, bs⟩ | ⟨hs, bs⟩ <;> rcases bit_cases K t with ⟨hk, bk⟩ | ⟨hk, bk⟩ <;>
    simp only [hs, hk, bs, bk, zero_nsmul, add_zero, one_nsmul, Bool.false_eq_true, ite_true, ite_false]
  · exact h2
  · exact pointAdd_rep h2 ha
  · exact pointAdd_rep h2 basePoint_rep
  · exact pointAdd_rep (pointAdd_rep h2 basePoint_rep) ha

theorem vladder_rep {S K : Nat} (hS : Below456 S) (hK : Below456 K) {a' : Point} {a : EPoint dZ}
    (ha : Rep a' a) :
    ∀ m ≤ 456, Rep (vladder S K a' m) ((S >>> (456 - m)) • baseAff + (K >>> (456 - m)) • a)
  | 0, _ => by
    rw [Nat.sub_zero, shift_456 hS, shift_456 hK, zero_nsmul, zero_nsmul, add_zero]
    exact identity_rep
  | m + 1, hm => by
    have h := vstepRef_rep (t := 455 - m) (show Rep (vladder S K a' m)
      ((S >>> (455 - m + 1)) • baseAff + (K >>> (455 - m + 1)) • a) by
      rw [show 455 - m + 1 = 456 - m by omega]; exact vladder_rep hS hK ha m (by omega)) ha
    rw [show 456 - (m + 1) = 455 - m by omega]
    exact h

theorem verifyEq_ok : VerifyEqOk := by
  intro pk sig ch a r hl hs hc ha hr
  have hva := decodePoint_valid ha
  have hS := decodeLE_below (bs := sig.drop 57) (by rw [List.length_drop, hs])
  have hQ := vladder_rep hS (decodeLE_below hc) (rep_toAffine (valid_negPoint hva)) 456 (Nat.le_refl _)
  rw [Nat.sub_self, Nat.shiftRight_zero, Nat.shiftRight_zero, toAffine_negPoint hva] at hQ
  exact verifyEquation_some hl hs hc ha hr hQ (rep_toAffine (decodePoint_valid hr))


/-- One bit of the four-iteration ladder: `Q` for the bits above `t` becomes
`Q` for the bits from `t` up. -/
theorem vstep4_rep {q a' r' : Point} {S K M t : Nat} {a r : EPoint dZ}
    (hq : Rep q ((S >>> (t + 1)) • baseAff + (K >>> (t + 1)) • a + (M >>> (t + 1)) • r))
    (ha : Rep a' a) (hr : Rep r' r) :
    Rep (vstep4 S K M t a' r' q) ((S >>> t) • baseAff + (K >>> t) • a + (M >>> t) • r) := by
  have h2 := pointAdd_rep hq hq
  have e1 : (S >>> t) • baseAff + (K >>> t) • a + (M >>> t) • r =
      ((S >>> (t + 1)) • baseAff + (K >>> (t + 1)) • a + (M >>> (t + 1)) • r) +
        ((S >>> (t + 1)) • baseAff + (K >>> (t + 1)) • a + (M >>> (t + 1)) • r) +
        ((S >>> t) &&& 1) • baseAff + ((K >>> t) &&& 1) • a + ((M >>> t) &&& 1) • r := by
    conv => lhs; rw [shift_step S t, shift_step K t, shift_step M t]
    rw [add_nsmul, add_nsmul, add_nsmul, two_mul, two_mul, two_mul, add_nsmul, add_nsmul, add_nsmul]
    abel
  rw [e1]
  unfold vstep4 vbit vphase
  simp only [show (0 : Nat) ≠ 3 from by decide, show (1 : Nat) ≠ 3 from by decide,
    show (2 : Nat) ≠ 3 from by decide, show (0 : Nat) ≠ 2 from by decide, show (0 : Nat) ≠ 1 from by decide,
    show (1 : Nat) ≠ 2 from by decide, ite_true, ite_false]
  rcases bit_cases S t with ⟨hs, bs⟩ | ⟨hs, bs⟩ <;> rcases bit_cases K t with ⟨hk, bk⟩ | ⟨hk, bk⟩ <;>
    rcases bit_cases M t with ⟨hm, bm⟩ | ⟨hm, bm⟩ <;>
    simp only [hs, hk, hm, bs, bk, bm, zero_nsmul, add_zero, one_nsmul, Bool.false_eq_true, ite_true,
      ite_false]
  · exact h2
  · exact pointAdd_rep h2 hr
  · exact pointAdd_rep h2 ha
  · exact pointAdd_rep (pointAdd_rep h2 ha) hr
  · exact pointAdd_rep h2 basePoint_rep
  · exact pointAdd_rep (pointAdd_rep h2 basePoint_rep) hr
  · exact pointAdd_rep (pointAdd_rep h2 basePoint_rep) ha
  · exact pointAdd_rep (pointAdd_rep (pointAdd_rep h2 basePoint_rep) ha) hr

theorem vladder4_rep {S K M : Nat} (hS : S >>> 458 = 0) (hK : K >>> 458 = 0) (hM : M >>> 458 = 0)
    {a' r' : Point} {a r : EPoint dZ} (ha : Rep a' a) (hr : Rep r' r) :
    ∀ m ≤ 458, Rep (vladder4 S K M a' r' m)
      ((S >>> (458 - m)) • baseAff + (K >>> (458 - m)) • a + (M >>> (458 - m)) • r)
  | 0, _ => by
    rw [Nat.sub_zero, hS, hK, hM, zero_nsmul, zero_nsmul, zero_nsmul, add_zero, add_zero]
    exact identity_rep
  | m + 1, hm => by
    have h := vstep4_rep (t := 457 - m) (show Rep (vladder4 S K M a' r' m)
      ((S >>> (457 - m + 1)) • baseAff + (K >>> (457 - m + 1)) • a + (M >>> (457 - m + 1)) • r) by
      rw [show 457 - m + 1 = 458 - m by omega]; exact vladder4_rep hS hK hM ha hr m (by omega)) ha hr
    rw [show 458 - (m + 1) = 457 - m by omega]
    exact h

theorem verifyEq4_ok : VerifyEq4Ok := by
  intro pk sig ch a r hl hs hc ha hr
  have hva := decodePoint_valid ha
  have hvr := decodePoint_valid hr
  have hS := decodeLE_below (bs := sig.drop 57) (by rw [List.length_drop, hs])
  have hK := decodeLE_below hc
  unfold Spec.Ed448.verifyEquation
  simp only [hl, hs, hc, bne_self_eq_false, Bool.or_false, Bool.false_eq_true, ite_false, ha, hr]
  refine congrArg (decide (Spec.Ed448.decodeLE (sig.drop 57) < Spec.Ed448.L) && ·) ?_
  generalize Spec.Ed448.decodeLE (sig.drop 57) = S at *
  generalize Spec.Ed448.decodeLE ch = K at *
  have h4 : ∀ x, (4 * x) >>> 458 = x >>> 456 := fun x => by
    rw [show 458 = 2 + 456 from rfl, Nat.shiftRight_add,
      show (4 * x) >>> 2 = x by rw [Nat.shiftRight_eq_div_pow]; omega]
  have hQ := vladder4_rep (S := 4 * S) (K := 4 * K) (M := 4) (by rw [h4]; exact shift_456 hS)
    (by rw [h4]; exact shift_456 hK)
    (by rw [show 458 = 3 + 455 from rfl, Nat.shiftRight_add, show (4 : Nat) >>> 3 = 0 by decide,
      Nat.zero_shiftRight])
    (rep_toAffine (valid_negPoint hva)) (rep_toAffine (valid_negPoint hvr)) 458 (Nat.le_refl _)
  rw [Nat.sub_self, Nat.shiftRight_zero, Nat.shiftRight_zero, Nat.shiftRight_zero, toAffine_negPoint hva,
    toAffine_negPoint hvr] at hQ
  have h1 := pointMul_rep 4 (pointMul_rep S basePoint_rep)
  have h2 := pointAdd_rep (pointMul_rep 4 (rep_toAffine hvr)) (pointMul_rep 4 (pointMul_rep K (rep_toAffine hva)))
  rw [Bool.eq_iff_iff, pointEqual_rep h1 h2, pointEqual_rep hQ identity_rep, Nat.mul_comm 4 S,
    Nat.mul_comm 4 K, mul_nsmul, mul_nsmul]
  constructor
  · intro h
    rw [h, smul_neg, smul_neg]; abel
  · intro h
    rw [smul_neg, smul_neg] at h
    rw [← sub_eq_zero, ← h]; abel

end VG.Proof.Ed448
