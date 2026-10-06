import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.P224.Prime
import VerifiedGarbage.Proof.P224.Point
import VerifiedGarbage.Proof.Weierstrass.Group
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-!
# P-224 is a curve the proofs apply to

`p` is prime (`Prime.lean`), and `x³ - 3x + b` has no root modulo `p`, so the
curve has no point of order 2 (a certificate for `noTwoTorsion_of_cert`:
`g = x^p` and the inverse `v` of `g - x` modulo `x³ - 3x + b`, found by
computer algebra and checked by the kernel). So its group law is the one the
proofs of the code take (`law`), which only the variant files
`Variants/P224/<Target>/Law.lean` import (the registration files are generic over it).
-/

namespace VG.Proof.P224

open Spec.Weierstrass Weierstrass

/-- The curve's field, as a literal: the elaborator would compute `2 ^ 224`
(above its threshold) to compare the curve's `p` with `Spec.P224.p`, or to
reduce `ZMod p`. -/
theorem curve_p : Spec.P224.curve.p = 26959946667150639794667015087019630673557916260026308143510066298881 := by
  decide +kernel

theorem curve_p_prime : Nat.Prime Spec.P224.curve.p := by
  rw [curve_p]
  exact prime_26959946667150639794667015087019630673557916260026308143510066298881

/-- `-b` modulo `p`. -/
private def negB : Nat :=
  8001660381584031794258346542525704258053235291346987067722831626317

/-- `x^p` modulo `x³ - 3x + b`. -/
private def xPow : Tri :=
  (13007951209251912699848910225737052564727108533249858001778075138108,
    6736638939299569244310158594083072418848545257754494280867682426394,
    20455971062524683444742559974151104391194361993401379142621028729827)

/-- The inverse of `x^p - x` modulo `x³ - 3x + b`. -/
private def xPowInv : Tri :=
  (1261710631285627074303005901530361786216288604486499842249704943048,
    4447412785031720342771701563499662000791675740805516550464163634437,
    9439789507511725786058244597052783711805086828869674293526675889612)

private theorem xPow_eq : powT Spec.P224.curve.p 3 negB 224 (0, 1, 0) Spec.P224.curve.p = xPow := by
  decide +kernel

private theorem xPowInv_mul : mulT Spec.P224.curve.p 3 negB xPowInv
    (xPow.1, (xPow.2.1 + Spec.P224.curve.p - 1) % Spec.P224.curve.p, xPow.2.2) = (1, 0, 0) := by
  decide +kernel

/-- The curve is `Good`: `x³ - 3x + b` has no root modulo `p`, by the
certificate (`Good.of_cert`, which states nothing in `ZMod p` here). -/
theorem good : Good Spec.P224.curve :=
  Good.of_cert Spec.P224.curve curve_p_prime (by rw [curve_p]; decide) 3 negB 224 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) xPow xPowInv xPow_eq xPowInv_mul

theorem law : Law Spec.P224.curve := good.law

end VG.Proof.P224
