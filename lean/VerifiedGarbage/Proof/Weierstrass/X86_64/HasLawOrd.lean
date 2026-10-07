import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
import VerifiedGarbage.Proof.Weierstrass.WindowJ

/-!
# A curve's group law, inversions and order, as a value

`HasLawInv` with the fact that every point of the curve has order `n`
(`OrdN`), which the window method in Jacobian coordinates needs: the variant
of a curve's interface on x86-64 for the curves whose functions use it
(`Variants/<Curve>/X86_64/Law.lean`).
-/

namespace VG.Proof.Weierstrass.X86_64

structure HasLawInvOrd (C : Spec.Weierstrass.Curve) : Type extends HasLawInv C where
  ord : OrdN C

end VG.Proof.Weierstrass.X86_64
