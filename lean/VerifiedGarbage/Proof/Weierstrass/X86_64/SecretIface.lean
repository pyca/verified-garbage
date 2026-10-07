import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
import VerifiedGarbage.Proof.Weierstrass.PeerOrder

/-! The facts needed by secret multiplication with arbitrary peer points. -/
namespace VG.Proof.Weierstrass.X86_64

structure HasSecretLawInv (C : Spec.Weierstrass.Curve) extends HasLawInv C where
  peerOrder : PeerOrder C

end VG.Proof.Weierstrass.X86_64
