import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.P384.Prime
import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.Weierstrass.Group
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-!
# P-384 is a curve the proofs apply to

`p` is prime (`Prime.lean`), and `x³ - 3x + b` has no root modulo `p`, so the
curve has no point of order 2 (a certificate for `noTwoTorsion_of_cert`:
`g = x^p` and the inverse `v` of `g - x` modulo `x³ - 3x + b`, found by
computer algebra and checked by the kernel). So its group law is the one the
proofs of the code take (`law`), which only the variant files
`Variants/P384/<Target>/Law.lean` import (the registration files are generic over it).
-/

namespace VG.Proof.P384

open Spec.Weierstrass Weierstrass

/-- The curve's field, as a literal: the elaborator would compute `2 ^ 384`
(above its threshold) to compare the curve's `p` with `Spec.P384.p`, or to
reduce `ZMod p`. -/
theorem curve_p : Spec.P384.curve.p =
    39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319 := by
  decide +kernel

theorem curve_p_prime : Nat.Prime Spec.P384.curve.p := by
  rw [curve_p]
  exact prime_39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319

/-- `-b` modulo `p`. -/
private def negB : Nat :=
  11821812636434773334430028259754565712022833414103878146519586102257032530187009463911005323375192894096167211881744

/-- `x^p` modulo `x³ - 3x + b`. -/
private def xPow : Tri :=
  (8300902441410358810024883245706595788071887638472987429650051756787010122663664392654234716054658334410824607717835,
    36451842499335230207230939190122359435795929611070366073564430331459357452117665764765104949638877581977396150453386,
    15550551877492060201127078427218509008503925815996229619149120823729355824416602968196515686102139833725391182697242)

/-- The inverse of `x^p - x` modulo `x³ - 3x + b`. -/
private def xPowInv : Tri :=
  (23037766613497683937702734290281044719364893268180251583910224888989381657771069200037813904257325918671976092329602,
    8235438212423615602427778915669574859600037698862346933589434399495169446996583974901273360826717582835190849638831,
    12157362177932134139146813183752135342286725243554133716818896354380897714709611791313184492360272402950851405460538)

private theorem xPow_eq : powT Spec.P384.curve.p 3 negB 384 (0, 1, 0) Spec.P384.curve.p = xPow := by
  decide +kernel

private theorem xPowInv_mul : mulT Spec.P384.curve.p 3 negB xPowInv
    (xPow.1, (xPow.2.1 + Spec.P384.curve.p - 1) % Spec.P384.curve.p, xPow.2.2) = (1, 0, 0) := by
  decide +kernel

/-- The curve is `Good`: `x³ - 3x + b` has no root modulo `p`, by the
certificate (`Good.of_cert`, which states nothing in `ZMod p` here). -/
theorem good : Good Spec.P384.curve :=
  Good.of_cert Spec.P384.curve curve_p_prime (by rw [curve_p]; decide) 3 negB 384 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) xPow xPowInv xPow_eq xPowInv_mul

theorem law : Law Spec.P384.curve := good.law

end VG.Proof.P384
