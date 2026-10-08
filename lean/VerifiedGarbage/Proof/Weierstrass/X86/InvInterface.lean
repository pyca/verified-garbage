import VerifiedGarbage.Proof.Weierstrass.X86.InvSpec
import VerifiedGarbage.Proof.Weierstrass.PrimeOrder

/-! Proof interface for prime-order curves, including inversion soundness. -/
namespace VG.Proof.Weierstrass.X86.Inv

structure HasLawInvOrd (C : Spec.Weierstrass.Curve) extends HasLawInv C where
  prime : PrimeOrder C

end VG.Proof.Weierstrass.X86.Inv
