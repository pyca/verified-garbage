import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.BrainpoolP512r1.Prime
import VerifiedGarbage.Proof.BrainpoolP512r1.Point
import VerifiedGarbage.Proof.Weierstrass.Group
import VerifiedGarbage.Proof.Weierstrass.Cubic

/-!
# brainpoolP512r1 is a curve the proofs apply to

`p` is prime (`Prime.lean`), and `x³ + a x + b` has no root modulo `p`, so the
curve has no point of order 2 (a certificate for `noTwoTorsion_of_cert`:
`g = x^p` and the inverse `v` of `g - x` modulo `x³ + a x + b`, found by
computer algebra and checked by the kernel). So its group law is the one the
proofs of the code take (`law`), which only the variant files
`Variants/BrainpoolP512r1/<Target>/Law.lean` import (the registration files are generic over it).
-/

namespace VG.Proof.BrainpoolP512r1

open Spec.Weierstrass Weierstrass

/-- The curve's field, as a literal: the elaborator would compute with `p`
(above its threshold) to compare the curve's `p` with `Spec.BrainpoolP512r1.p`, or to
reduce `ZMod p`. -/
theorem curve_p : Spec.BrainpoolP512r1.curve.p = 8948962207650232551656602815159153422162609644098354511344597187200057010413552439917934304191956942765446530386427345937963894309923928536070534607816947 := by
  decide +kernel

theorem curve_p_prime : Nat.Prime Spec.BrainpoolP512r1.curve.p := by
  rw [curve_p]
  exact prime_8948962207650232551656602815159153422162609644098354511344597187200057010413552439917934304191956942765446530386427345937963894309923928536070534607816947

/-- `-a` modulo `p`. -/
private def negA : Nat :=
  2654101649677169323990181508682774098087893873475608284207686741749755096132276341889943335783972980074294676707863468103742060282484210298004808763552809

/-- `-b` modulo `p`. -/
private def negB : Nat :=
  5703173199321265492381753230817075505630700634460852593016273518463877833830288943454409175703674331205645756879453574140199082811088933301729003745530320

/-- `x^p` modulo `x³ + a x + b`. -/
private def xPow : Tri :=
  (1171207495004172184870350888846736138287303023485176906012618281211713437683792754554487831602135902082002900222626154888623984832190465825804542440156758,
    8084232344484297400096973808713771151807802980077000277155885356866384898318055411291502310474576666020856034767232292921921200356795942821699510525638530,
    8946525268153297803678489203520925023466257242991388711508304401945186994333131060379100434708771280975428123247921998263945934840348532173621471775822375)

/-- The inverse of `x^p - x` modulo `x³ + a x + b`. -/
private def xPowInv : Tri :=
  (1803314254406975735450288165685996255159518649509801042516748854645051387409671406770237299640480790704019033082794117735071555073817603589011800439246700,
    5423510712171489546644718125848465800445423157029586731376840833885116518002476487579816819625716701205282987784671943974892074197635932083426899437475869,
    1980640283309979095730852824049519563548238190526698414050554203846063330593484879663419473345296546803597274808794758955751942903882298593095810355797106)

private theorem xPow_eq : powT Spec.BrainpoolP512r1.curve.p negA negB 512 (0, 1, 0) Spec.BrainpoolP512r1.curve.p = xPow := by
  decide +kernel

private theorem xPowInv_mul : mulT Spec.BrainpoolP512r1.curve.p negA negB xPowInv
    (xPow.1, (xPow.2.1 + Spec.BrainpoolP512r1.curve.p - 1) % Spec.BrainpoolP512r1.curve.p, xPow.2.2) = (1, 0, 0) := by
  decide +kernel

/-- The curve is `Good`: `x³ + a x + b` has no root modulo `p`, by the
certificate (`Good.of_cert`, which states nothing in `ZMod p` here). -/
theorem good : Good Spec.BrainpoolP512r1.curve :=
  Good.of_cert Spec.BrainpoolP512r1.curve curve_p_prime (by rw [curve_p]; decide) negA negB 512 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) xPow xPowInv xPow_eq xPowInv_mul

theorem law : Law Spec.BrainpoolP512r1.curve := good.law

end VG.Proof.BrainpoolP512r1
