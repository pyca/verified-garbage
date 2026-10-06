import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.BrainpoolP384r1.Prime
import VerifiedGarbage.Proof.BrainpoolP384r1.Point
import VerifiedGarbage.Proof.Weierstrass.Group
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-!
# brainpoolP384r1 is a curve the proofs apply to

`p` is prime (`Prime.lean`), and `x³ + a x + b` has no root modulo `p`, so the
curve has no point of order 2 (a certificate for `noTwoTorsion_of_cert`:
`g = x^p` and the inverse `v` of `g - x` modulo `x³ + a x + b`, found by
computer algebra and checked by the kernel). So its group law is the one the
proofs of the code take (`law`), which only the variant files
`Variants/BrainpoolP384r1/<Target>/Law.lean` import (the registration files are generic over it).
-/

namespace VG.Proof.BrainpoolP384r1

open Spec.Weierstrass Weierstrass

/-- The curve's field, as a literal: the elaborator would compute with `p`
(above its threshold) to compare the curve's `p` with `Spec.BrainpoolP384r1.p`, or to
reduce `ZMod p`. -/
theorem curve_p : Spec.BrainpoolP384r1.curve.p = 21659270770119316173069236842332604979796116387017648600081618503821089934025961822236561982844534088440708417973331 := by
  decide +kernel

theorem curve_p_prime : Nat.Prime Spec.BrainpoolP384r1.curve.p := by
  rw [curve_p]
  exact prime_21659270770119316173069236842332604979796116387017648600081618503821089934025961822236561982844534088440708417973331

/-- `-a` modulo `p`. -/
private def negA : Nat :=
  2610291730521071877789955317311056531572656531832425707992085991374752909090535788598219135866672173564987199570989

/-- `-b` modulo `p`. -/
private def negB : Nat :=
  20942138915226687079740064800278915318369473570620200579237210552582040317534372214534105522044775205974636771123266

/-- `x^p` modulo `x³ + a x + b`. -/
private def xPow : Tri :=
  (15298734606309199264420805533508030890414563944865334671512276287980469130952691092095033434054904617589085651229424,
    11068186017202743673118810097581550772766737817903064248079785514094454210086250096998177788174923242769800729139125,
    5443622384506312450156513124064629656210090739227743791001374481785671329407903472242873611627734644954640700142187)

/-- The inverse of `x^p - x` modulo `x³ + a x + b`. -/
private def xPowInv : Tri :=
  (18045346159989301294719205289786962596468003789292587159741834949006371209014629163014746348076599162029150578683262,
    1976113098210081074617925902571799281931794102930411075466637102904693541261693854282593756972459711385728480861278,
    4643256948357306801182104578797069499791313285794868896678261438458615860465573791712519540292328347437871877550575)

private theorem xPow_eq : powT Spec.BrainpoolP384r1.curve.p negA negB 384 (0, 1, 0) Spec.BrainpoolP384r1.curve.p = xPow := by
  decide +kernel

private theorem xPowInv_mul : mulT Spec.BrainpoolP384r1.curve.p negA negB xPowInv
    (xPow.1, (xPow.2.1 + Spec.BrainpoolP384r1.curve.p - 1) % Spec.BrainpoolP384r1.curve.p, xPow.2.2) = (1, 0, 0) := by
  decide +kernel

/-- The curve is `Good`: `x³ + a x + b` has no root modulo `p`, by the
certificate (`Good.of_cert`, which states nothing in `ZMod p` here). -/
theorem good : Good Spec.BrainpoolP384r1.curve :=
  Good.of_cert Spec.BrainpoolP384r1.curve curve_p_prime (by rw [curve_p]; decide) negA negB 384 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) xPow xPowInv xPow_eq xPowInv_mul

theorem law : Law Spec.BrainpoolP384r1.curve := good.law

end VG.Proof.BrainpoolP384r1
