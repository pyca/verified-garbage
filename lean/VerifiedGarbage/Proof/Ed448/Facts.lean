import VerifiedGarbage.Proof.Ed448.Group.Decode
import Mathlib.Tactic.Abel
import VerifiedGarbage.Proof.Ed448.Signing

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.VerifyEq`. -/
section

/-!
# Ed448: the verification equation, as code checks it

`verifyEquation` (RFC 8032 §5.2.7, cofactored) in terms of what code
computes: for decoded `A` and `R`, `[4]([S]B + [k](-A))` against `[4]R`,
each doubled twice from representatives `Q` and `R`. Over the group
`[4]([S]B - [k]A) = [4]R` exactly when `[4][S]B = [4]R + [4][k]A`.
-/

namespace VG.Proof.Ed448

open Spec.X448 (Fe P)
open Spec.Ed448 (Point)
open EdwardsLaw

theorem four_smul {a : EPoint dZ} : (a + a) + (a + a) = 4 • a := by
  rw [show (4 : Nat) = 1 + 1 + 1 + 1 from rfl, add_nsmul, add_nsmul, add_nsmul, one_nsmul]
  abel

theorem verifyEquation_some {pk sig ch : List Byte} (hl : pk.length = 57) (hs : sig.length = 114)
    (hc : ch.length = 57) {a r : Point} (ha : Spec.Ed448.decodePoint pk = some a)
    (hr : Spec.Ed448.decodePoint (sig.take 57) = some r) {Q R : Point}
    (hQ : Rep Q (Spec.Ed448.decodeLE (sig.drop 57) • baseAff +
      Spec.Ed448.decodeLE ch • (-toAffine a))) (hR : Rep R (toAffine r)) :
    Spec.Ed448.verifyEquation pk sig ch =
      (decide (Spec.Ed448.decodeLE (sig.drop 57) < Spec.Ed448.L) &&
        Spec.Ed448.pointEqual (double (double Q)) (double (double R))) := by
  have hva := decodePoint_valid ha
  have hvr := decodePoint_valid hr
  unfold Spec.Ed448.verifyEquation
  simp only [hl, hs, hc, bne_self_eq_false, Bool.or_false, Bool.false_eq_true, ite_false, ha, hr]
  refine congrArg (decide (Spec.Ed448.decodeLE (sig.drop 57) < Spec.Ed448.L) && ·) ?_
  generalize Spec.Ed448.decodeLE (sig.drop 57) = S at *
  generalize Spec.Ed448.decodeLE ch = K at *
  have h1 := pointMul_rep 4 (pointMul_rep S basePoint_rep)
  have h2 := pointAdd_rep (pointMul_rep 4 (rep_toAffine hvr)) (pointMul_rep 4 (pointMul_rep K (rep_toAffine hva)))
  have h3 := double_rep (double_rep hQ)
  have h4 := double_rep (double_rep hR)
  rw [Bool.eq_iff_iff, pointEqual_rep h1 h2, pointEqual_rep h3 h4, VG.Proof.Ed448.four_smul, VG.Proof.Ed448.four_smul]
  constructor
  · intro h
    rw [smul_add, smul_neg, h]; abel
  · intro h
    have : 4 • (S • baseAff) = 4 • (S • baseAff + K • -toAffine a) + 4 • (K • toAffine a) := by
      rw [smul_add (4 : Nat) (S • baseAff), smul_neg]; abel
    rw [this, h]

end VG.Proof.Ed448

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Facts`. -/
section

/-!
# Ed448: the reference computations agree with the specification

Untrusted and target-independent, and heavy: the group law over `ZMod p`.
The facts `Ref.lean` states, which every target's proofs take as hypotheses:

* `recover_ok`: `recoverX` is `recoverRef` (ring identities);
* `baseLadder_ok`: after the top `m` bits of `k`, `ladder` represents
  `[k >> (456 - m)]B` (`ladder_rep`), so the whole ladder encodes `[k]B`;
* `verifyEq_ok`: `vladder` represents `[S >> n]B + [k >> n]a` the same way,
  and the equation follows (`verifyEquation_some`).

Only registration files import this module.
-/

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

theorem recover_ok : RecoverOk := fun y sign => by rw [VG.Proof.Ed448.recoverX_eq]; rfl

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
    conv => lhs; rw [VG.Proof.Ed448.shift_step k t]
    rw [add_nsmul, two_mul, add_nsmul]
  rw [e1]
  rcases VG.Proof.Ed448.bit_cases k t with ⟨h, hb⟩ | ⟨h, hb⟩
  · rw [h, zero_nsmul, add_zero, hb]; exact h2
  · rw [h, one_nsmul, hb]; exact pointAdd_rep h2 basePoint_rep

theorem ladder_rep {k : Nat} (hk : Below456 k) :
    ∀ m ≤ 456, Rep (ladder k m) ((k >>> (456 - m)) • baseAff)
  | 0, _ => by rw [Nat.sub_zero, shift_456 hk, zero_nsmul]; exact identity_rep
  | m + 1, hm => by
    have h := VG.Proof.Ed448.ladderStep_rep (t := 455 - m) (show Rep (ladder k m) ((k >>> (455 - m + 1)) • baseAff) by
      rw [show 455 - m + 1 = 456 - m by omega]; exact VG.Proof.Ed448.ladder_rep hk m (by omega))
    rw [show 456 - (m + 1) = 455 - m by omega]
    exact h

theorem baseLadder_ok : BaseLadderOk := fun k hk => by
  have h := VG.Proof.Ed448.ladder_rep hk 456 (Nat.le_refl _)
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
    conv => lhs; rw [VG.Proof.Ed448.shift_step S t, VG.Proof.Ed448.shift_step K t]
    rw [add_nsmul, add_nsmul, two_mul, two_mul, add_nsmul, add_nsmul]
    abel
  rw [e1]
  unfold vstepRef
  rcases VG.Proof.Ed448.bit_cases S t with ⟨hs, bs⟩ | ⟨hs, bs⟩ <;> rcases VG.Proof.Ed448.bit_cases K t with ⟨hk, bk⟩ | ⟨hk, bk⟩ <;>
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
    have h := VG.Proof.Ed448.vstepRef_rep (t := 455 - m) (show Rep (vladder S K a' m)
      ((S >>> (455 - m + 1)) • baseAff + (K >>> (455 - m + 1)) • a) by
      rw [show 455 - m + 1 = 456 - m by omega]; exact VG.Proof.Ed448.vladder_rep hS hK ha m (by omega)) ha
    rw [show 456 - (m + 1) = 455 - m by omega]
    exact h

theorem verifyEq_ok : VerifyEqOk := by
  intro pk sig ch a r hl hs hc ha hr
  have hva := decodePoint_valid ha
  have hS := decodeLE_below (bs := sig.drop 57) (by rw [List.length_drop, hs])
  have hQ := VG.Proof.Ed448.vladder_rep hS (decodeLE_below hc) (rep_toAffine (valid_negPoint hva)) 456 (Nat.le_refl _)
  rw [Nat.sub_self, Nat.shiftRight_zero, Nat.shiftRight_zero, toAffine_negPoint hva] at hQ
  exact VG.Proof.Ed448.verifyEquation_some hl hs hc ha hr hQ (rep_toAffine (decodePoint_valid hr))

end VG.Proof.Ed448

end
