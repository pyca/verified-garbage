module

public import VerifiedGarbage.Proof.Weierstrass.Complete
public import VerifiedGarbage.Spec.BrainpoolP320r1
import VerifiedGarbage.Proof.BrainpoolP320r1.Prime
import VerifiedGarbage.Proof.Weierstrass.Group
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-!
# brainpoolP320r1 is a curve the proofs apply to

`p` is prime (`Prime.lean`), and `x³ + a x + b` has no root modulo `p`, so the
curve has no point of order 2 (a certificate for `noTwoTorsion_of_cert`:
`g = x^p` and the inverse `v` of `g - x` modulo `x³ + a x + b`, found by
computer algebra and checked by the kernel). So its group law is the one the
proofs of the code take (`law`), which only the modules
`Proof/BrainpoolP320r1/<Target>/Law.lean` import, privately (the registration files import those).
-/

@[expose] public section

namespace VG.Proof.BrainpoolP320r1

open Spec.Weierstrass Weierstrass

/-- The curve's field, as a literal: the elaborator would compute with `p`
(above its threshold) to compare the curve's `p` with `Spec.BrainpoolP320r1.p`, or to
reduce `ZMod p`. -/
theorem curve_p : Spec.BrainpoolP320r1.curve.p = 1763593322239166354161909842446019520889512772719515192772960415288640868802149818095501499903527 := by
  decide +kernel

theorem curve_p_prime : Nat.Prime Spec.BrainpoolP320r1.curve.p := by
  rw [curve_p]
  exact prime_1763593322239166354161909842446019520889512772719515192772960415288640868802149818095501499903527

/-- `-a` modulo `p`. -/
private def negA : Nat :=
  1238884003799773661055990124927975761946272608307397819782649083973869358153345752339147188412275

/-- `-b` modulo `p`. -/
private def negB : Nat :=
  1079132482047959302022180751329024110006015359999508828477246819225641001005408682176211765509249

/-- `x^p` modulo `x³ + a x + b`. -/
private def xPow : Tri :=
  (941283314030726626609609621346469610223376685281248632749168619445872674242087311956580719672896,
    1627505711339090958068949504235466202138282780514312010937439761318614283544393875555582922899404,
    1478809040336180117610597128272015811705574462988368552684549269059586078146293821365194795370582)

/-- The inverse of `x^p - x` modulo `x³ + a x + b`. -/
private def xPowInv : Tri :=
  (122870849904181773089670971022562028177776873262791750757648614230269868632418475396154339683393,
    723011386214059723890258847105443730712169077323097966906237591005955893472217848824699974159717,
    591398295572457992264474255279168440779894522159829821427394627523920432340975599627340802408935)

private theorem xPow_eq : powT Spec.BrainpoolP320r1.curve.p negA negB 320 (0, 1, 0) Spec.BrainpoolP320r1.curve.p = xPow := by
  decide +kernel

private theorem xPowInv_mul : mulT Spec.BrainpoolP320r1.curve.p negA negB xPowInv
    (xPow.1, (xPow.2.1 + Spec.BrainpoolP320r1.curve.p - 1) % Spec.BrainpoolP320r1.curve.p, xPow.2.2) = (1, 0, 0) := by
  decide +kernel

/-- The curve is `Good`: `x³ + a x + b` has no root modulo `p`, by the
certificate (`Good.of_cert`, which states nothing in `ZMod p` here). -/
theorem good : Good Spec.BrainpoolP320r1.curve :=
  Good.of_cert Spec.BrainpoolP320r1.curve curve_p_prime (by rw [curve_p]; decide) negA negB 320 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) xPow xPowInv xPow_eq xPowInv_mul

theorem law : Law Spec.BrainpoolP320r1.curve := good.law

end VG.Proof.BrainpoolP320r1
