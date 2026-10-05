import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.P521.Prime
import VerifiedGarbage.Proof.P521.Point
import VerifiedGarbage.Proof.Weierstrass.Group
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-!
# P-521 is a curve the proofs apply to

`p` is prime (`Prime.lean`), and `x³ - 3x + b` has no root modulo `p`, so the
curve has no point of order 2 (a certificate for `noTwoTorsion_of_cert`:
`g = x^p` and the inverse `v` of `g - x` modulo `x³ - 3x + b`, found by
computer algebra and checked by the kernel). So its group law is the one the
proofs of the code take (`law`), which only the variant files
`Variants/P521/<Target>/Law.lean` import (the registration files are generic over it).
-/

namespace VG.Proof.P521

open Spec.Weierstrass Weierstrass

/-- The curve's field, as a literal: the elaborator would compute `2 ^ 521`
(above its threshold) to compare the curve's `p` with `Spec.P521.p`, or to
reduce `ZMod p`. -/
theorem curve_p : Spec.P521.curve.p =
    6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151 := by
  decide +kernel

theorem curve_p_prime : Nat.Prime Spec.P521.curve.p := by
  rw [curve_p]
  exact prime_6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151

/-- `-b` modulo `p`. -/
private def negB : Nat :=
  5770948622056875440470788408314587647333227701191621660399877064689590067246921036108850903087694931728704179094774544727683535468125630900431700802636071167

/-- `x^p` modulo `x³ - 3x + b`. -/
private def xPow : Tri :=
  (4860891086045056853561103990765776437896461732719963324290057395732751086103788161954116339572232800690457337429123819664279834135875092463554593205804047047,
    5623913033336113422386236864006719062755991763864609197545100619433248161746017032673051834216465799515469811516542321474225029959858163827729884161696537584,
    1001953287042776430710398404157808389686486783711671042552203031726396048646933945084221650544610877143419486981178519186421076931920775674509717542655505052)

/-- The inverse of `x^p - x` modulo `x³ - 3x + b`. -/
private def xPowInv : Tri :=
  (5556850081864827842302249485475501585472702946772625307642304195702912034363837867267334216347521692509406916620096684956176894315447091116492501000392161958,
    2592645775458497527836362227091103884154287512470494672274301275565663408730650270660448980645397363205839490313252565391972848223674401530161387302727484004,
    3919380404691066388712376322317341026252002696138380915147944189379687824774581460974855590730258562532022938584569429027963361353339635641909491533809725330)

private theorem xPow_eq : powT Spec.P521.curve.p 3 negB 521 (0, 1, 0) Spec.P521.curve.p = xPow := by
  decide +kernel

private theorem xPowInv_mul : mulT Spec.P521.curve.p 3 negB xPowInv
    (xPow.1, (xPow.2.1 + Spec.P521.curve.p - 1) % Spec.P521.curve.p, xPow.2.2) = (1, 0, 0) := by
  decide +kernel

/-- The curve is `Good`: `x³ - 3x + b` has no root modulo `p`, by the
certificate (`Good.of_cert`, which states nothing in `ZMod p` here). -/
theorem good : Good Spec.P521.curve :=
  Good.of_cert Spec.P521.curve curve_p_prime (by rw [curve_p]; decide) 3 negB 521 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) xPow xPowInv xPow_eq xPowInv_mul

theorem law : Law Spec.P521.curve := good.law

end VG.Proof.P521
