import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.P192.Prime
import VerifiedGarbage.Proof.P192.Point
import VerifiedGarbage.Proof.Weierstrass.Group
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-!
# P-192 is a curve the proofs apply to

`p` is prime (`Prime.lean`), and `x³ - 3x + b` has no root modulo `p`, so the
curve has no point of order 2 (a certificate for `noTwoTorsion_of_cert`:
`g = x^p` and the inverse `v` of `g - x` modulo `x³ - 3x + b`, found by
computer algebra and checked by the kernel). So its group law is the one the
proofs of the code take (`law`), which only the variant files
`Variants/P192/<Target>/Law.lean` import (the registration files are generic over it).
-/

namespace VG.Proof.P192

open Spec.Weierstrass Weierstrass

/-- The curve's field, as a literal: the elaborator would compute with `p`
(`2 ^ 192`, above its threshold) to compare the curve's `p` with `Spec.P192.p`, or to
reduce `ZMod p`. -/
theorem curve_p : Spec.P192.curve.p = 6277101735386680763835789423207666416083908700390324961279 := by
  decide +kernel

theorem curve_p_prime : Nat.Prime Spec.P192.curve.p := by
  rw [curve_p]
  exact prime_6277101735386680763835789423207666416083908700390324961279

/-- `-b` modulo `p`. -/
private def negB : Nat :=
  3821946189377736946095495508010214631314800642229133723214

/-- `x^p` modulo `x³ - 3x + b`. -/
private def xPow : Tri :=
  (897772426216857905740464718317648918394375021027244704353,
    6216008227648530967744815138875139188844756526337129907353,
    2689664654584911429047662352445008748844766839681540128463)

/-- The inverse of `x^p - x` modulo `x³ - 3x + b`. -/
private def xPowInv : Tri :=
  (3076984081099336410538445874700673783096882824010410041625,
    4871298686935519674170250204910228760438566091784467946767,
    105597762148406811168096478311383789005400348177979944870)

private theorem xPow_eq : powT Spec.P192.curve.p 3 negB 192 (0, 1, 0) Spec.P192.curve.p = xPow := by
  decide +kernel

private theorem xPowInv_mul : mulT Spec.P192.curve.p 3 negB xPowInv
    (xPow.1, (xPow.2.1 + Spec.P192.curve.p - 1) % Spec.P192.curve.p, xPow.2.2) = (1, 0, 0) := by
  decide +kernel

/-- The curve is `Good`: `x³ - 3x + b` has no root modulo `p`, by the
certificate (`Good.of_cert`, which states nothing in `ZMod p` here). -/
theorem good : Good Spec.P192.curve :=
  Good.of_cert Spec.P192.curve curve_p_prime (by rw [curve_p]; decide) 3 negB 192 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) xPow xPowInv xPow_eq xPowInv_mul

theorem law : Law Spec.P192.curve := good.law

end VG.Proof.P192
