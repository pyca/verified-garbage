import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Secp256k1.Prime
import VerifiedGarbage.Proof.Secp256k1.Point
import VerifiedGarbage.Proof.Weierstrass.Group
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-!
# secp256k1 is a curve the proofs apply to

`p` is prime (`Prime.lean`), and `x³ + 7` has no root modulo `p`, so the
curve has no point of order 2 (a certificate for `noTwoTorsion_of_cert`:
`g = x^p` and the inverse `v` of `g - x` modulo `x³ + 7`, found by
computer algebra and checked by the kernel). So its group law is the one the
proofs of the code take (`law`), which only the variant files
`Variants/Secp256k1/<Target>/Law.lean` import (the registration files are generic over it).
-/

namespace VG.Proof.Secp256k1

open Spec.Weierstrass Weierstrass

/-- The curve's field, as a literal: the elaborator would compute `2 ^ 256`
(above its threshold) to compare the curve's `p` with `Spec.Secp256k1.p`, or to
reduce `ZMod p`. -/
theorem curve_p : Spec.Secp256k1.curve.p = 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  decide +kernel

theorem curve_p_prime : Nat.Prime Spec.Secp256k1.curve.p := by
  rw [curve_p]
  exact prime_115792089237316195423570985008687907853269984665640564039457584007908834671663

/-- `-b` modulo `p`. -/
private def negB : Nat := 115792089237316195423570985008687907853269984665640564039457584007908834671656

/-- `x^p` modulo `x³ + 7`. -/
private def xPow : Tri := (0, 55594575648329892869085402983802832744385952214688224221778511981742606582254, 0)

/-- The inverse of `x^p - x` modulo `x³ + 7`. -/
private def xPowInv : Tri := (0, 0, 46758632835564736012269203954919337884311706168562511263687580192619680188360)

private theorem xPow_eq : powT Spec.Secp256k1.curve.p 0 negB 256 (0, 1, 0) Spec.Secp256k1.curve.p = xPow := by
  decide +kernel

private theorem xPowInv_mul : mulT Spec.Secp256k1.curve.p 0 negB xPowInv
    (xPow.1, (xPow.2.1 + Spec.Secp256k1.curve.p - 1) % Spec.Secp256k1.curve.p, xPow.2.2) = (1, 0, 0) := by
  decide +kernel

/-- The curve is `Good`: `x³ + 7` has no root modulo `p`, by the
certificate (`Good.of_cert`, which states nothing in `ZMod p` here). -/
theorem good : Good Spec.Secp256k1.curve :=
  Good.of_cert Spec.Secp256k1.curve curve_p_prime (by rw [curve_p]; decide) 0 negB 256 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) xPow xPowInv xPow_eq xPowInv_mul

theorem law : Law Spec.Secp256k1.curve := good.law

end VG.Proof.Secp256k1
