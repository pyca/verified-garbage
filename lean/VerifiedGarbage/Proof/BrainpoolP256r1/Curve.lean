import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.BrainpoolP256r1.Prime
import VerifiedGarbage.Proof.BrainpoolP256r1.Point
import VerifiedGarbage.Proof.Weierstrass.Group
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-!
# brainpoolP256r1 is a curve the proofs apply to

`p` is prime (`Prime.lean`), and `x³ + a x + b` has no root modulo `p`, so the
curve has no point of order 2 (a certificate for `noTwoTorsion_of_cert`:
`g = x^p` and the inverse `v` of `g - x` modulo `x³ + a x + b`, found by
computer algebra and checked by the kernel). So its group law is the one the
proofs of the code take (`law`), which only the variant files
`Variants/BrainpoolP256r1/<Target>/Law.lean` import (the registration files are generic over it).
-/

namespace VG.Proof.BrainpoolP256r1

open Spec.Weierstrass Weierstrass

/-- The curve's field, as a literal: the elaborator would compute with `p`
(above its threshold) to compare the curve's `p` with `Spec.BrainpoolP256r1.p`, or to
reduce `ZMod p`. -/
theorem curve_p : Spec.BrainpoolP256r1.curve.p = 76884956397045344220809746629001649093037950200943055203735601445031516197751 := by
  decide +kernel

theorem curve_p_prime : Nat.Prime Spec.BrainpoolP256r1.curve.p := by
  rw [curve_p]
  exact prime_76884956397045344220809746629001649093037950200943055203735601445031516197751

/-- `-a` modulo `p`. -/
private def negA : Nat :=
  20186768791719234177182518232823303015917335661467841094348773256267632057758

/-- `-b` modulo `p`. -/
private def negB : Nat :=
  59307723899723505379734048839207128830087524142019970636688749144398190758849

/-- `x^p` modulo `x³ + a x + b`. -/
private def xPow : Tri :=
  (6934312191461072874148100761682709823469295718683001920214272321718106639743,
    74730866787797357883289511930108312968771754820441431075655545456776372037232,
    24103594246436844333297699615940947720531226414641076004148624174016432703105)

/-- The inverse of `x^p - x` modulo `x³ + a x + b`. -/
private def xPowInv : Tri :=
  (5347744486777530706669047377084680431416082047222058099865314757079289018413,
    36567706687211352878623830248023275230139348886519930341788893933933071887964,
    57300115342307814829368171194017451425362166738975514114819334576929185469628)

private theorem xPow_eq : powT Spec.BrainpoolP256r1.curve.p negA negB 256 (0, 1, 0) Spec.BrainpoolP256r1.curve.p = xPow := by
  decide +kernel

private theorem xPowInv_mul : mulT Spec.BrainpoolP256r1.curve.p negA negB xPowInv
    (xPow.1, (xPow.2.1 + Spec.BrainpoolP256r1.curve.p - 1) % Spec.BrainpoolP256r1.curve.p, xPow.2.2) = (1, 0, 0) := by
  decide +kernel

/-- The curve is `Good`: `x³ + a x + b` has no root modulo `p`, by the
certificate (`Good.of_cert`, which states nothing in `ZMod p` here). -/
theorem good : Good Spec.BrainpoolP256r1.curve :=
  Good.of_cert Spec.BrainpoolP256r1.curve curve_p_prime (by rw [curve_p]; decide) negA negB 256 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) xPow xPowInv xPow_eq xPowInv_mul

theorem law : Law Spec.BrainpoolP256r1.curve := good.law

end VG.Proof.BrainpoolP256r1
